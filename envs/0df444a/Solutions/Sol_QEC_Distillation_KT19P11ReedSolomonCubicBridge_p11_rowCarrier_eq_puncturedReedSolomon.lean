-- Prove2me | solution 1 for QEC.Distillation.KT19P11ReedSolomonCubicBridge.p11_rowCarrier_eq_puncturedReedSolomon
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T13:02:26.971711+00:00
-- url     : https://prove2.me/submissions/6e4a3cc5-a464-4c74-8075-6ff923c2670b

import Definitions.Def_QEC_Coding_ReedSolomon_Punctured
import Definitions.Def_QEC_Distillation_PrimeQuditProtocol_CubicCSS
import Definitions.Def_QEC_Distillation_PrimeQuditProtocol_P11CubicBridge
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_KT19ReedSolomon_evaluation_mem_reedSolomonCode
import Theorems.Thm_QEC_Coding_KT19ReedSolomon_mem_reedSolomonCode
import Theorems.Thm_QEC_Coding_KT19ReedSolomon_puncturedReedSolomonCode_dimension
import Theorems.Thm_QEC_Coding_KT19ReedSolomon_shortenedReedSolomonCode_le_puncturedReedSolomonCode
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
private theorem p11_logical_mem_punctured (index : Fin 2) :
    p11LogicalRow index ∈ (puncturedReedSolomonCode 11 4 2).carrier := by
  apply (mem_puncturedReedSolomonCode _).2
  refine ⟨evaluationLinearMap 11 4 ⟨p11LogicalPolynomial index,
      p11_logical_degreeLT index⟩, ?_, ?_⟩
  · exact evaluation_mem_reedSolomonCode 11 4 _
  · rfl
private theorem p11_rowCarrier_le_punctured :
    p11RowCarrier ≤ (puncturedReedSolomonCode 11 4 2).carrier := by
  rw [p11RowCarrier]
  apply Submodule.span_le.2
  rintro word ⟨index, rfl⟩
  rcases index with index | index
  · exact p11_logical_mem_punctured index
  · exact (shortenedReedSolomonCode_le_puncturedReedSolomonCode 11 4 2)
      (p11_stabilizer_mem_shortened index)
private theorem p11_rows_linearIndependent :
    LinearIndependent (ZMod 11) p11Row := by
  rw [Fintype.linearIndependent_iff]
  intro coefficient hzero index
  let u : Fin 2 → ZMod 11 := fun logical => coefficient (Sum.inl logical)
  let h : Fin 2 → ZMod 11 := fun stabilizer => coefficient (Sum.inr stabilizer)
  have hsplit :
      (∑ logical : Fin 2, u logical • p11LogicalRow logical) +
        ∑ stabilizer : Fin 2, h stabilizer • p11StabilizerRow stabilizer = 0 := by
    simpa [u, h, p11Row, Fintype.sum_sum_type] using hzero
  rcases p11_rows_independent u h hsplit with ⟨hu, hh⟩
  rcases index with index | index
  · simpa [u] using congrFun hu index
  · simpa [h] using congrFun hh index
private theorem p11_rowCarrier_finrank :
    Module.finrank (ZMod 11) p11RowCarrier = 4 := by
  rw [p11RowCarrier]
  simpa using finrank_span_eq_card p11_rows_linearIndependent
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
    p11RowCarrier = (puncturedReedSolomonCode 11 4 2).carrier := by
  apply Submodule.eq_of_le_of_finrank_eq p11_rowCarrier_le_punctured
  rw [p11_rowCarrier_finrank]
  simpa [Dimension_eq_finrank_carrier] using
    (puncturedReedSolomonCode_dimension 11 4 2 (by norm_num) (by norm_num)).symm
end QEC.Distillation.KT19P11ReedSolomonCubicBridge
