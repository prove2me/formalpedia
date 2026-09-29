-- Prove2me | solution 1 for R03SlotHallLift.p3Factor_implies_graph_center_hall
-- status  : ACCEPTED   (prove)
-- author  : @hao jia
-- created : 2026-09-17T11:14:00.438441+00:00
-- url     : https://prove2.me/submissions/65805c25-c72a-48f1-a555-369c018571b9

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

theorem graph_center_hall_lifts_to_p3Factor
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


end
end R03SlotHallLift

open R03SlotHallLift
open CubicP3Partition
universe u
variable {V : Type u} [Fintype V]
open scoped Classical
theorem solution
    (G : SimpleGraph V) (F : P3Factor G) :
    ∃ C : Finset V,
      Fintype.card V = 3 * C.card ∧ GraphCenterHallCondition G C := by
  classical
  let b := F.blockCount
  let middle : Fin b → V := fun i => F.place (i, 1)
  let C : Finset V := Finset.univ.image middle
  have hmiddle_mem (i : Fin b) : middle i ∈ C := by
    exact Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩
  let eC : Fin b ≃ Center C :=
    Equiv.ofBijective
      (fun i => ⟨middle i, hmiddle_mem i⟩)
      (by
        constructor
        · intro i j hij
          have hv : middle i = middle j := congrArg Subtype.val hij
          have hp : (i, (1 : Fin 3)) = (j, 1) := by
            apply F.place.injective
            simpa [middle] using hv
          exact congrArg Prod.fst hp
        · intro c
          obtain ⟨i, hi, hci⟩ := Finset.mem_image.mp c.property
          exact ⟨i, Subtype.ext hci⟩)
  have hCcard : C.card = b := by
    simpa only [Fintype.card_fin, Fintype.card_coe] using
      (Fintype.card_congr eC).symm
  have hVcard : Fintype.card V = 3 * b := by
    have hp := Fintype.card_congr F.place
    simp only [Fintype.card_prod, Fintype.card_fin] at hp
    omega
  have hC : Fintype.card V = 3 * C.card := by
    simpa [hCcard] using hVcard
  have hnot_middle (i : Fin b) (j : Fin 3) (hj : j ≠ 1) :
      F.place (i, j) ∉ C := by
    intro hc
    obtain ⟨k, hk, hkc⟩ := Finset.mem_image.mp hc
    have hp : (i, j) = (k, (1 : Fin 3)) := by
      apply F.place.injective
      simpa [middle] using hkc.symm
    exact hj (congrArg Prod.snd hp)
  let f : Slot C → Leaf C := fun s =>
    if hs : s.2 = 0 then
      ⟨F.place (eC.symm s.1, 0), hnot_middle (eC.symm s.1) 0 (by decide)⟩
    else
      ⟨F.place (eC.symm s.1, 2), hnot_middle (eC.symm s.1) 2 (by decide)⟩
  have hf_inj : Function.Injective f := by
    intro s t hst
    rcases s with ⟨s, p⟩
    rcases t with ⟨t, q⟩
    fin_cases p <;> fin_cases q
    · have hv : F.place (eC.symm s, (0 : Fin 3)) =
          F.place (eC.symm t, 0) := congrArg Subtype.val hst
      have hp : (eC.symm s, (0 : Fin 3)) = (eC.symm t, 0) :=
        F.place.injective hv
      exact Prod.ext (eC.symm.injective (congrArg Prod.fst hp)) rfl
    · have hv : F.place (eC.symm s, (0 : Fin 3)) =
          F.place (eC.symm t, 2) := congrArg Subtype.val hst
      have hp : (eC.symm s, (0 : Fin 3)) = (eC.symm t, 2) :=
        F.place.injective hv
      have hj := congrArg Prod.snd hp
      have hj' : (0 : Fin 3) = 2 := by simpa using hj
      exfalso
      exact (by decide : (0 : Fin 3) ≠ 2) hj'
    · have hv : F.place (eC.symm s, (2 : Fin 3)) =
          F.place (eC.symm t, 0) := congrArg Subtype.val hst
      have hp : (eC.symm s, (2 : Fin 3)) = (eC.symm t, 0) :=
        F.place.injective hv
      have hj := congrArg Prod.snd hp
      have hj' : (2 : Fin 3) = 0 := by simpa using hj
      exfalso
      exact (by decide : (2 : Fin 3) ≠ 0) hj'
    · have hv : F.place (eC.symm s, (2 : Fin 3)) =
          F.place (eC.symm t, 2) := congrArg Subtype.val hst
      have hp : (eC.symm s, (2 : Fin 3)) = (eC.symm t, 2) :=
        F.place.injective hv
      exact Prod.ext (eC.symm.injective (congrArg Prod.fst hp)) rfl
  have hf_surj : Function.Surjective f := by
    intro w
    obtain ⟨x, hx⟩ := F.place.surjective w.1
    rcases x with ⟨i, j⟩
    fin_cases j
    · refine ⟨(eC i, 0), ?_⟩
      simp [f]
      exact Subtype.ext hx
    · exfalso
      apply w.property
      rw [← hx]
      exact hmiddle_mem i
    · refine ⟨(eC i, 1), ?_⟩
      simp [f]
      exact Subtype.ext hx
  have hcenter (s : Center C) :
      (s : V) = F.place (eC.symm s, (1 : Fin 3)) := by
    change (s : V) = middle (eC.symm s)
    exact (congrArg Subtype.val (eC.apply_symm_apply s)).symm
  let R : V → Fin 2 → V → Prop := fun c _ w => G.Adj c w
  have hmatch : BijectiveSlotMatching R C := by
    refine ⟨f, ⟨hf_inj, hf_surj⟩, ?_⟩
    intro s
    rcases s with ⟨s, p⟩
    fin_cases p
    · change G.Adj (s : V) (F.place (eC.symm s, (0 : Fin 3)))
      rw [hcenter s]
      exact (G.adj_comm _ _).mp (F.edge01 (eC.symm s))
    · change G.Adj (s : V) (F.place (eC.symm s, (2 : Fin 3)))
      rw [hcenter s]
      exact F.edge12 (eC.symm s)
  have hcard : Fintype.card (Slot C) = Fintype.card (Leaf C) :=
    balanced_slot_leaf_card C hC
  have hHallR : HallCondition R C :=
    (hall_iff_bijectiveSlotMatching R C hcard).mpr hmatch
  refine ⟨C, hC, ?_⟩
  simpa [GraphCenterHallCondition, R, slotRel] using hHallR
