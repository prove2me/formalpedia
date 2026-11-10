-- Prove2me | solution 1 for QEC.Distillation.KT19P11ReedSolomonCubicBridge.p11_retainedAllOnes_mem_rowCarrier
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T13:02:32.145645+00:00
-- url     : https://prove2.me/submissions/98f03479-4850-4737-a0c0-1d150c85f1f3

import Definitions.Def_QEC_Coding_ReedSolomon_Punctured
import Definitions.Def_QEC_Distillation_PrimeQuditProtocol_CubicCSS
import Definitions.Def_QEC_Distillation_PrimeQuditProtocol_P11CubicBridge
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_KT19ReedSolomon_mem_reedSolomonCode
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Coding.KT19ReedSolomon.mem_reedSolomonCode
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator



set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.KT19P11ReedSolomonCubicBridge
open QEC.Coding
open QEC.Coding.KT19ReedSolomon
open QEC.Distillation.KT19PrimeQuditCSS
open scoped BigOperators
attribute [local instance] QEC.Distillation.KT19P11ReedSolomonCubicBridge.p11Prime
attribute [local instance] QEC.Distillation.KT19P11ReedSolomonCubicBridge.p11NeZero
attribute [local instance] QEC.Distillation.KT19P11ReedSolomonCubicBridge.p11PrimeQuditRegisterLabelFintype
attribute [local instance] p11Prime p11NeZero p11PrimeQuditRegisterLabelFintype
namespace QEC.Distillation.KT19P11ReedSolomonCubicBridge
theorem _root_.solution :
    (1 : Word (ZMod 11) (KeptPunctureLocation 11 2)) ∈ p11RowCarrier := by
  have hzero : p11LogicalRow 0 ∈ p11RowCarrier := by
    rw [p11RowCarrier]
    exact Submodule.subset_span ⟨Sum.inl 0, rfl⟩
  have hone : p11LogicalRow 1 ∈ p11RowCarrier := by
    rw [p11RowCarrier]
    exact Submodule.subset_span ⟨Sum.inl 1, rfl⟩
  have hcombination : -p11LogicalRow 0 - p11LogicalRow 1 ∈ p11RowCarrier :=
    p11RowCarrier.sub_mem (p11RowCarrier.neg_mem hzero) hone
  convert hcombination using 1
  ext point
  simp [p11LogicalRow, p11RetainedEvaluation, p11LogicalPolynomial, evaluationMap]
end QEC.Distillation.KT19P11ReedSolomonCubicBridge
