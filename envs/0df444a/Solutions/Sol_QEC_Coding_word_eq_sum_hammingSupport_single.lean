-- Prove2me | solution 1 for QEC.Coding.word_eq_sum_hammingSupport_single
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:57:12.582646+00:00
-- url     : https://prove2.me/submissions/ae032164-bed0-42c8-9ab9-55a9c7590cf6

import Definitions.Def_QEC_Coding_CodeReduction_Classical_Collapse
import Definitions.Def_QEC_Coding_ChainComplex_HomotopyDistance
import Definitions.Def_QEC_Coding_CodeReduction_Classical_Distance
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_boundary_single
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_linearMapOfBasisImages_single
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_originalBoundary_single
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
    {F : Type u} [Field F] [DecidableEq F]
    {ι : Type v} [Fintype ι] [DecidableEq ι] (x : Word F ι) :
    x = ∑ i ∈ hammingSupport x, Pi.single i (x i) := by
  classical
  ext j
  rw [Finset.sum_apply]
  by_cases hj : x j = 0
  · have hjnot : j ∉ hammingSupport x := by simp [hammingSupport, hj]
    rw [hj]
    simp [hjnot]
  · have hjmem : j ∈ hammingSupport x := by simp [hammingSupport, hj]
    rw [Finset.sum_eq_single j]
    · simp
    · intro i hi hij
      simp [Ne.symm hij]
    · exact fun h => (h hjmem).elim
end QEC.Coding
