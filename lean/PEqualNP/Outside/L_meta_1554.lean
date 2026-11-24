import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1554

private abbrev Point := Fin 13
private def line (t : Point) : Finset Point := {t, t + 1, t + 3, t + 9}
private abbrev pencil : Finset Point := {0, 4, 10, 12}
private def direction (v : Point) : Point :=
  (![0,0,12,0,4,4,10,4,12,0,10,10,12] : Fin 13 → Point) v

private lemma direction_mem : ∀ v, direction v ∈ pencil ∧ v ∈ line (direction v) := by
  decide +kernel

private lemma direction_unique :
    ∀ v : Point, v ≠ 0 → ∀ t ∈ pencil, v ∈ line t → direction v = t := by
  decide +kernel

private lemma center_mem : ∀ t ∈ pencil, (0 : Point) ∈ line t := by decide +kernel

private abbrev crossing (x : Point → Bool) : Prop :=
  ∃ a b : Point, (a ≠ 0 ∧ b ≠ 0 ∧ ¬ ∃ t ∈ pencil, a ∈ line t ∧ b ∈ line t) ∧
    x a = true ∧ x b = true

private lemma crossing_iff (x : Point → Bool) :
    crossing x ↔ ¬ ∃ t ∈ pencil, ∀ v : Point, x v = true → v ∈ line t := by
  constructor
  · rintro ⟨a,b,⟨_,_,hab⟩,ha,hb⟩ ⟨t,ht,h⟩
    exact hab ⟨t,ht,h a ha,h b hb⟩
  · intro h
    have witness (t : Point) (ht : t ∈ pencil) : ∃ v, x v = true ∧ v ∉ line t := by
      by_contra! hw
      exact h ⟨t,ht,hw⟩
    obtain ⟨a,ha,ha'⟩ := witness 0 (by decide)
    have ha0 : a ≠ 0 := fun e => ha' (e ▸ center_mem 0 (by decide))
    obtain ⟨ht,_⟩ := direction_mem a
    obtain ⟨b,hb,hb'⟩ := witness (direction a) ht
    have hb0 : b ≠ 0 := fun e => hb' (e ▸ center_mem (direction a) ht)
    refine ⟨a,b,⟨ha0,hb0,?_⟩,ha,hb⟩
    rintro ⟨t,ht',hat',hbt'⟩
    exact hb' (direction_unique a ha0 t ht' hat' ▸ hbt')

private lemma crossing_mono (x y : Point → Bool) (h : crossing x)
    (hle : ∀ v, x v = true → y v = true) : crossing y := by
  obtain ⟨a,b,hab,ha,hb⟩ := h
  exact ⟨a,b,hab,hle a ha,hle b hb⟩

private def support (x : Point → Bool) : Finset Point :=
  Finset.univ.filter (fun v => x v = true)

private lemma support_bij : Function.Bijective support := by
  constructor
  · intro x y h
    funext v
    have hh : (x v = true) ↔ (y v = true) := by
      simpa [support] using (show v ∈ support x ↔ v ∈ support y by rw [h])
    cases hx : x v <;> cases hy : y v <;> simp_all
  · intro s
    refine ⟨fun v => decide (v ∈ s), ?_⟩
    ext v
    simp [support]

private def containedSupports : Finset (Finset Point) :=
  (line 0).powerset ∪ (line 4).powerset ∪ (line 10).powerset ∪ (line 12).powerset

private lemma contained_count : containedSupports.card = 58 := by decide +kernel

private lemma crossing_count :
    (Finset.univ.filter crossing).card = 8134 := by
  have complement_card :
      (Finset.univ.filter fun x : Point → Bool => ¬ crossing x).card = 58 := by
    rw [← contained_count]
    apply Finset.card_bijective support support_bij
    intro x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, crossing_iff, not_not,
      containedSupports, Finset.mem_union, Finset.mem_powerset]
    have sub (t : Point) : support x ⊆ line t ↔ ∀ v, x v = true → v ∈ line t := by
      simp [support, Finset.subset_iff]
    simp only [sub, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨t, rfl | rfl | rfl | rfl, ht⟩ <;> tauto
    · intro h
      rcases h with ((h | h) | h) | h
      · exact ⟨0, by simp, h⟩
      · exact ⟨4, by simp, h⟩
      · exact ⟨10, by simp, h⟩
      · exact ⟨12, by simp, h⟩
  have total : (Finset.univ : Finset (Point → Bool)).card = 8192 := by
    simp [Point]
  have eq := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Point → Bool))) crossing
  omega

private lemma outside_cross : ∀ t, crossing (fun v => decide (v ∉ line t)) := by
  decide +kernel

end PEqualNP.Outside.L_meta_1554

open PEqualNP.Outside.L_meta_1554

theorem PEqualNP.Outside.L_meta_1554 : ∀ L : Fin 13 → Finset (Fin 13), (∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) →
    (∀ x : Fin 13 → Bool, (∃ a b : Fin 13, (a ≠ 0 ∧ b ≠ 0 ∧ ¬ ∃ t ∈ ({0, 4, 10, 12} : Finset (Fin 13)), a ∈ L t ∧ b ∈ L t) ∧ x a = true ∧ x b = true) ↔ ¬ ∃ t ∈ ({0, 4, 10, 12} : Finset (Fin 13)), ∀ v : Fin 13, x v = true → v ∈ L t) ∧
    (Finset.univ.filter (fun x : Fin 13 → Bool => (∃ a b : Fin 13, (a ≠ 0 ∧ b ≠ 0 ∧ ¬ ∃ t ∈ ({0, 4, 10, 12} : Finset (Fin 13)), a ∈ L t ∧ b ∈ L t) ∧ x a = true ∧ x b = true))).card = 8134 ∧
    (∀ x y : Fin 13 → Bool, (∃ a b : Fin 13, (a ≠ 0 ∧ b ≠ 0 ∧ ¬ ∃ t ∈ ({0, 4, 10, 12} : Finset (Fin 13)), a ∈ L t ∧ b ∈ L t) ∧ x a = true ∧ x b = true) → (∀ v : Fin 13, x v = true → y v = true) → (∃ a b : Fin 13, (a ≠ 0 ∧ b ≠ 0 ∧ ¬ ∃ t ∈ ({0, 4, 10, 12} : Finset (Fin 13)), a ∈ L t ∧ b ∈ L t) ∧ y a = true ∧ y b = true)) ∧
    (∀ t : Fin 13, (∃ a b : Fin 13, (a ≠ 0 ∧ b ≠ 0 ∧ ¬ ∃ t ∈ ({0, 4, 10, 12} : Finset (Fin 13)), a ∈ L t ∧ b ∈ L t) ∧ (fun v : Fin 13 => decide (v ∉ L t)) a = true ∧ (fun v : Fin 13 => decide (v ∉ L t)) b = true) ∧ ∀ p ∈ L t, (∃ a b : Fin 13, (a ≠ 0 ∧ b ≠ 0 ∧ ¬ ∃ t ∈ ({0, 4, 10, 12} : Finset (Fin 13)), a ∈ L t ∧ b ∈ L t) ∧ (fun v : Fin 13 => decide (v ∉ L t ∨ v = p)) a = true ∧ (fun v : Fin 13 => decide (v ∉ L t ∨ v = p)) b = true)) := by
  intro L hL
  have eq : L = line := funext hL
  subst L
  exact ⟨crossing_iff, crossing_count, crossing_mono, fun t =>
    ⟨outside_cross t, fun p _ => crossing_mono _ _ (outside_cross t) (by simp; grind)⟩⟩
