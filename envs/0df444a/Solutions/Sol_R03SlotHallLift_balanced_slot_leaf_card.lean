-- Prove2me | solution 1 for R03SlotHallLift.balanced_slot_leaf_card
-- status  : ACCEPTED   (prove)
-- author  : @hao jia
-- created : 2026-09-17T10:48:19.769777+00:00
-- url     : https://prove2.me/submissions/78a41604-1223-4c5b-a028-fe0d95af4194

import Mathlib
import Definitions.Def_cubic_p3_partition_models
import Definitions.Def_r03_defs_809c83f713_sp05_port_balanced_slot_factor_lift_formalizatio

namespace R03SlotHallLift

open CubicP3Partition

universe u

variable {V : Type u} [Fintype V]

noncomputable section
open scoped Classical

theorem hall_iff_slotMatching (R : V → Fin 2 → V → Prop) (C : Finset V) :
    HallCondition R C ↔ SlotMatching R C := by
  classical
  simpa [HallCondition, SlotMatching] using
    (Fintype.all_card_le_filter_rel_iff_exists_injective
      (fun s w => slotRel R C s w))

theorem hall_iff_bijectiveSlotMatching
    (R : V → Fin 2 → V → Prop) (C : Finset V)
    (hcard : Fintype.card (Slot C) = Fintype.card (Leaf C)) :
    HallCondition R C ↔ BijectiveSlotMatching R C := by
  constructor
  · intro h
    obtain ⟨f, hf_inj, hf_rel⟩ := (hall_iff_slotMatching R C).mp h
    refine ⟨f, ?_, hf_rel⟩
    exact (Fintype.bijective_iff_injective_and_card f).2 ⟨hf_inj, hcard⟩
  · rintro ⟨f, hf_bij, hf_rel⟩
    apply (hall_iff_slotMatching R C).mpr
    exact ⟨f, hf_bij.1, hf_rel⟩

lemma placeFun_injective
    (C : Finset V) (eC : Fin C.card ≃ Center C) (f : Slot C ≃ Leaf C) :
    Function.Injective (placeFun C eC f) := by
  intro x y hxy
  rcases x with ⟨i, j⟩
  rcases y with ⟨i', j'⟩
  fin_cases j <;> fin_cases j'
  · simp [placeFun] at hxy
    have hp : f (eC i, 0) = f (eC i', 0) := Subtype.ext hxy
    have hpi := f.injective hp
    have hi := eC.injective (congrArg Prod.fst hpi)
    exact Prod.ext hi rfl
  · simp [placeFun] at hxy
    exfalso
    apply (f (eC i, 0)).property
    rw [hxy]
    exact (eC i').property
  · simp [placeFun] at hxy
    have hp : f (eC i, 0) = f (eC i', 1) := Subtype.ext hxy
    have hs : (0 : Fin 2) = 1 := by
      simpa using congrArg Prod.snd (f.injective hp)
    exfalso
    exact Fin.zero_ne_one hs
  · simp [placeFun] at hxy
    exfalso
    apply (f (eC i', 0)).property
    rw [← hxy]
    exact (eC i).property
  · simp [placeFun] at hxy
    exact Prod.ext hxy rfl
  · simp [placeFun] at hxy
    exfalso
    apply (f (eC i', 1)).property
    rw [← hxy]
    exact (eC i).property
  · simp [placeFun] at hxy
    have hp : f (eC i, 1) = f (eC i', 0) := Subtype.ext hxy
    have hs : (1 : Fin 2) = 0 := by
      simpa using congrArg Prod.snd (f.injective hp)
    exfalso
    exact Fin.zero_ne_one hs.symm
  · simp [placeFun] at hxy
    exfalso
    apply (f (eC i, 1)).property
    rw [hxy]
    exact (eC i').property
  · simp [placeFun] at hxy
    have hp : f (eC i, 1) = f (eC i', 1) := Subtype.ext hxy
    have hpi := f.injective hp
    have hi := eC.injective (congrArg Prod.fst hpi)
    exact Prod.ext hi rfl

lemma card_slot_eq_two_mul (C : Finset V) :
    Fintype.card (Slot C) = 2 * C.card := by
  simp [Slot, Center, Fintype.card_prod, Fintype.card_fin]
  omega

lemma card_leaf_eq_card_sub (C : Finset V) :
    Fintype.card (Leaf C) = Fintype.card V - C.card := by
  simpa [Center, Leaf] using
    (Fintype.card_subtype_compl (p := fun v : V => v ∈ C))


end
end R03SlotHallLift

open R03SlotHallLift
open CubicP3Partition
universe u
variable {V : Type u} [Fintype V]
open scoped Classical
theorem solution
    (C : Finset V) (hC : Fintype.card V = 3 * C.card) :
    Fintype.card (Slot C) = Fintype.card (Leaf C) := by
  rw [card_slot_eq_two_mul, card_leaf_eq_card_sub, hC]
  omega
