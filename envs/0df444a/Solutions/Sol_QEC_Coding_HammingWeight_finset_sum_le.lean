-- Prove2me | solution 1 for QEC.Coding.HammingWeight_finset_sum_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:56:45.634381+00:00
-- url     : https://prove2.me/submissions/c690924a-1ee7-4fad-aefc-35e8b7fce8a7

import Definitions.Def_QEC_Coding_CodeReduction_Classical_Collapse
import Definitions.Def_QEC_Coding_ChainComplex_HomotopyDistance
import Definitions.Def_QEC_Coding_CodeReduction_Classical_Distance
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_boundary_single
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_linearMapOfBasisImages_single
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_originalBoundary_single
import Theorems.Thm_QEC_Coding_HammingWeight_add_le
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Coding.ClassicalWeightReduction.boundary_single
attribute [local simp] QEC.Coding.ClassicalWeightReduction.linearMapOfBasisImages_single
attribute [local simp] QEC.Coding.ClassicalWeightReduction.originalBoundary_single
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator



set_option autoImplicit false
open QEC QEC.Coding
open scoped BigOperators
universe u v w
namespace QEC.Coding
theorem _root_.solution
    {F : Type u} [AddCommGroup F] [DecidableEq F]
    {ι : Type v} [Fintype ι]
    {κ : Type w} (s : Finset κ) (x : κ → Word F ι) :
    HammingWeight (∑ k ∈ s, x k) ≤ ∑ k ∈ s, HammingWeight (x k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert k s hk ih =>
      rw [Finset.sum_insert hk, Finset.sum_insert hk]
      exact (HammingWeight_add_le (x k) (∑ j ∈ s, x j)).trans
        (Nat.add_le_add_left ih _)
end QEC.Coding
