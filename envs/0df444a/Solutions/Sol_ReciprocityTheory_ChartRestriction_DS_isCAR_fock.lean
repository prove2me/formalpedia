-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.isCAR_fock
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:52:44.510419+00:00
-- url     : https://prove2.me/submissions/6833e49a-4148-4606-bed1-49f72b5ad785

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CarSumSqZeroOfAnti
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_InhabCAR

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution : IsCAR (cpFock (n := n)) cmFock := by
  intro i a j b
  refine ⟨?_, ?_, ?_⟩
  · refine LinearMap.ext fun z => ?_
    simp only [LinearMap.add_apply, Module.End.mul_apply, cpFock, LinearMap.mulLeft_apply,
      LinearMap.zero_apply]
    rw [← mul_assoc, ← mul_assoc, ← add_mul, ExteriorAlgebra.ι_add_mul_swap, zero_mul]
  · refine LinearMap.ext fun z => ?_
    simp only [LinearMap.add_apply, Module.End.mul_apply, cmFock, LinearMap.zero_apply]
    rw [CliffordAlgebra.contractLeft_comm, neg_add_cancel]
  · refine LinearMap.ext fun z => ?_
    simp only [LinearMap.add_apply, Module.End.mul_apply, cmFock, cpFock, LinearMap.mulLeft_apply]
    rw [CliffordAlgebra.contractLeft_ι_mul, sub_add_cancel]
    by_cases h : i = j ∧ a = b
    · obtain ⟨rfl, rfl⟩ := h
      simp
    · rw [if_neg h]
      have hne : (i, a) ≠ (j, b) := fun e => h ⟨congrArg Prod.fst e, congrArg Prod.snd e⟩
      simp [LinearMap.proj_apply, Pi.single_apply, hne]
end ReciprocityTheory.ChartRestriction.DS
