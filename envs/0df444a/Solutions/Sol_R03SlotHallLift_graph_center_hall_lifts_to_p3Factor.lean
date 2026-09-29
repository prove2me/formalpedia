-- Prove2me | solution 1 for R03SlotHallLift.graph_center_hall_lifts_to_p3Factor
-- status  : ACCEPTED   (prove)
-- author  : @hao jia
-- created : 2026-09-17T11:13:48.919234+00:00
-- url     : https://prove2.me/submissions/db0c3c4b-c8c0-4d4d-b4e0-0a8949d67b82

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

lemma balanced_slot_leaf_card
    (C : Finset V) (hC : Fintype.card V = 3 * C.card) :
    Fintype.card (Slot C) = Fintype.card (Leaf C) := by
  rw [card_slot_eq_two_mul, card_leaf_eq_card_sub, hC]
  omega

theorem bijective_slot_matching_lifts_to_p3Factor
    (G : SimpleGraph V) (R : V → Fin 2 → V → Prop) (C : Finset V)
    (hC : Fintype.card V = 3 * C.card)
    (hR : ∀ s w, slotRel R C s w → G.Adj s.1.1 w.1)
    (hmatch : BijectiveSlotMatching R C) :
    Nonempty (P3Factor G) := by
  classical
  obtain ⟨f, hf, hrel⟩ := hmatch
  let fEquiv : Slot C ≃ Leaf C := Equiv.ofBijective f hf
  let eC : Fin C.card ≃ Center C := by
    simpa only [Fintype.card_coe] using (Fintype.equivFin (Center C)).symm
  let p : Fin C.card × Fin 3 → V := placeFun C eC fEquiv
  have hp_inj : Function.Injective p := placeFun_injective C eC fEquiv
  have hp_card : Fintype.card (Fin C.card × Fin 3) = Fintype.card V := by
    simp [Fintype.card_prod, Fintype.card_fin, hC]
    omega
  have hp_bij : Function.Bijective p :=
    (Fintype.bijective_iff_injective_and_card p).2 ⟨hp_inj, hp_card⟩
  let pEquiv : (Fin C.card × Fin 3) ≃ V := Equiv.ofBijective p hp_bij
  refine ⟨{ blockCount := C.card, place := pEquiv, edge01 := ?_, edge12 := ?_ }⟩
  · intro i
    have h := hR (eC i, 0) (fEquiv (eC i, 0)) (hrel (eC i, 0))
    exact (G.adj_comm _ _).mp h
  · intro i
    exact hR (eC i, 1) (fEquiv (eC i, 1)) (hrel (eC i, 1))

end
end R03SlotHallLift

open R03SlotHallLift
open CubicP3Partition
universe u
variable {V : Type u} [Fintype V]
open scoped Classical
theorem solution
    (G : SimpleGraph V) (C : Finset V)
    (hC : Fintype.card V = 3 * C.card)
    (hHall : GraphCenterHallCondition G C) :
    Nonempty (P3Factor G) := by
  let R : V → Fin 2 → V → Prop := fun c _ w => G.Adj c w
  have hHallR : HallCondition R C := by
    intro A
    simpa [R, slotRel, GraphCenterHallCondition] using hHall A
  have hcard : Fintype.card (Slot C) = Fintype.card (Leaf C) :=
    balanced_slot_leaf_card C hC
  have hmatch : BijectiveSlotMatching R C :=
    (hall_iff_bijectiveSlotMatching R C hcard).mp hHallR
  apply bijective_slot_matching_lifts_to_p3Factor G R C hC
  · intro s w hs
    exact hs
  · exact hmatch
