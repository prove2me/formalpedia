-- Prove2me | solution 1 for QEC.Coding.hammingSupport_smul_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:57:11.554202+00:00
-- url     : https://prove2.me/submissions/084d01db-ea2f-43f7-b0b0-79b8de713d71

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
    {F : Type u} [Field F]
    {ι : Type v} [Fintype ι] [DecidableEq F]
    (a : F) (x : Word F ι) :
    hammingSupport (a • x) ⊆ hammingSupport x := by
  intro i hi
  simp only [hammingSupport, Finset.mem_filter, Finset.mem_univ, true_and,
    Pi.smul_apply, smul_eq_mul] at hi ⊢
  intro hxi
  exact hi (by simp [hxi])
end QEC.Coding
