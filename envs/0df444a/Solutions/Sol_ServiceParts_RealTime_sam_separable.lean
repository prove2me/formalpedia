-- Prove2me | solution 1 for ServiceParts.RealTime.sam_separable
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T07:48:07.418305+00:00
-- url     : https://prove2.me/submissions/b6341ca0-80f1-49c0-93d7-278f21864c7b

import Mathlib
import Definitions.Def_ServiceParts_RealTime_Model
import Definitions.Def_ServiceParts_RealTime_SAM

set_option autoImplicit false

open MeasureTheory ServiceParts.RealTime in
theorem solution {I J : Type*} [Fintype I] [Fintype J] {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (M : I → ItemModel J Ω P) :
    (∀ y : I → J → ℕ → ℕ, IsMultiSAMOptimal M y ↔ ∀ i, IsSAMOptimal (M i) (y i)) ∧
      ∀ y z : I → J → ℕ → ℕ, IsMultiSAMOptimal M y → (∀ i, IsSAMOptimal (M i) (z i)) →
        multiSamObjective M y = ∑ i, samObjective (M i) (z i) := by
  classical
  have key : ∀ y : I → J → ℕ → ℕ, IsMultiSAMOptimal M y ↔ ∀ i, IsSAMOptimal (M i) (y i) := by
    intro y
    constructor
    · rintro ⟨hf, hopt⟩ i
      refine ⟨hf i, ?_⟩
      intro y' hy'
      have hfeas : MultiSAMFeasible M (Function.update y i y') := by
        intro k
        by_cases hk : k = i
        · subst hk; simpa using hy'
        · simpa [Function.update_of_ne hk] using hf k
      have h := hopt _ hfeas
      unfold multiSamObjective at h
      have e1 : ∀ k, samObjective (M k) (Function.update y i y' k)
          = Function.update (fun k => samObjective (M k) (y k)) i (samObjective (M i) y') k := by
        intro k
        by_cases hk : k = i
        · subst hk; simp
        · simp [Function.update_of_ne hk]
      simp_rw [e1] at h
      rw [Finset.sum_update_of_mem (Finset.mem_univ i)] at h
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at h
      have : Finset.univ \ {i} = Finset.univ.erase i := by
        ext x; simp
      rw [this] at h
      linarith
    · intro h
      refine ⟨fun i => (h i).1, ?_⟩
      intro y' hy'
      unfold multiSamObjective
      exact Finset.sum_le_sum fun i _ => (h i).2 (y' i) (hy' i)
  refine ⟨key, ?_⟩
  intro y z hy hz
  have hy' := (key y).1 hy
  unfold multiSamObjective
  refine Finset.sum_congr rfl fun i _ => ?_
  exact le_antisymm ((hy' i).2 _ (hz i).1) ((hz i).2 _ (hy' i).1)
