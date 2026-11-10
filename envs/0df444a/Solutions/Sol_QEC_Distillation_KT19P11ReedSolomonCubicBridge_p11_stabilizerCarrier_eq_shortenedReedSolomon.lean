-- Prove2me | solution 1 for QEC.Distillation.KT19P11ReedSolomonCubicBridge.p11_stabilizerCarrier_eq_shortenedReedSolomon
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T13:02:11.920043+00:00
-- url     : https://prove2.me/submissions/8972dc5d-0b0d-49da-b3f6-0332cb3a7608

import Definitions.Def_QEC_Coding_ReedSolomon_Punctured
import Definitions.Def_QEC_Distillation_PrimeQuditProtocol_CubicCSS
import Definitions.Def_QEC_Distillation_PrimeQuditProtocol_P11CubicBridge
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_KT19ReedSolomon_evaluation_mem_reedSolomonCode
import Theorems.Thm_QEC_Coding_KT19ReedSolomon_mem_reedSolomonCode
import Theorems.Thm_QEC_Coding_KT19ReedSolomon_shortenedReedSolomonCode_dimension
import Theorems.Thm_QEC_Distillation_EncodedCode_ImplementsLogicalGate_symm
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Coding.KT19ReedSolomon.mem_reedSolomonCode
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator


section
noncomputable section
namespace QEC.Distillation.KT19P11ReedSolomonCubicBridge
open QEC.Coding
open QEC.Coding.KT19ReedSolomon
open QEC.Distillation.KT19PrimeQuditCSS
open scoped BigOperators
attribute [local instance] p11Prime p11NeZero p11PrimeQuditRegisterLabelFintype
private theorem p11_stabilizer_mem_shortened (index : Fin 2) :
    p11StabilizerRow index ∈ (shortenedReedSolomonCode 11 4 2).carrier := by
  apply (mem_shortenedReedSolomonCode _).2
  refine ⟨evaluationLinearMap 11 4 ⟨p11StabilizerPolynomial index,
      p11_stabilizer_degreeLT index⟩, ?_, ?_, ?_⟩
  · exact evaluation_mem_reedSolomonCode 11 4 _
  · exact p11_stabilizer_restrictSelected_zero index
  · rfl
private theorem p11_stabilizerCarrier_le_shortened :
    p11StabilizerCarrier ≤ (shortenedReedSolomonCode 11 4 2).carrier := by
  rw [p11StabilizerCarrier]
  apply Submodule.span_le.2
  rintro word ⟨index, rfl⟩
  exact p11_stabilizer_mem_shortened index
private theorem p11_stabilizer_rows_linearIndependent :
    LinearIndependent (ZMod 11) p11StabilizerRow := by
  rw [Fintype.linearIndependent_iff]
  intro h hzero index
  have hboth := p11_rows_independent 0 h (by simpa using hzero)
  simpa using congrFun hboth.2 index
private theorem p11_stabilizerCarrier_finrank :
    Module.finrank (ZMod 11) p11StabilizerCarrier = 2 := by
  rw [p11StabilizerCarrier]
  simpa using finrank_span_eq_card p11_stabilizer_rows_linearIndependent
end QEC.Distillation.KT19P11ReedSolomonCubicBridge
end
end

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
    p11StabilizerCarrier = (shortenedReedSolomonCode 11 4 2).carrier := by
  apply Submodule.eq_of_le_of_finrank_eq p11_stabilizerCarrier_le_shortened
  rw [p11_stabilizerCarrier_finrank]
  simpa [Dimension_eq_finrank_carrier] using
    (shortenedReedSolomonCode_dimension 11 4 2 (by norm_num) (by norm_num) (by norm_num)).symm
end QEC.Distillation.KT19P11ReedSolomonCubicBridge
