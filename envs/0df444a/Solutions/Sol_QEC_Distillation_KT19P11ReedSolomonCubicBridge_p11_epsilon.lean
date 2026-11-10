-- Prove2me | solution 1 for QEC.Distillation.KT19P11ReedSolomonCubicBridge.p11_epsilon
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T13:02:54.893646+00:00
-- url     : https://prove2.me/submissions/02903751-18c8-4e17-896b-cc70a104279c

import Definitions.Def_QEC_Coding_ReedSolomon_Punctured
import Definitions.Def_QEC_Distillation_PrimeQuditProtocol_CubicCSS
import Definitions.Def_QEC_Distillation_PrimeQuditProtocol_P11CubicBridge
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_KT19ReedSolomon_mem_reedSolomonCode
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
private theorem p11_logical_selected_cube_sum (index : Fin 2) :
    (∑ point : {point : ZMod 11 // point ∈ selectedPunctureLocations 11 2},
      evaluationMap 11 (p11LogicalPolynomial index) point.1 *
        evaluationMap 11 (p11LogicalPolynomial index) point.1 *
          evaluationMap 11 (p11LogicalPolynomial index) point.1) = -1 := by
  calc
    (∑ point : {point : ZMod 11 // point ∈ selectedPunctureLocations 11 2},
      evaluationMap 11 (p11LogicalPolynomial index) point.1 *
        evaluationMap 11 (p11LogicalPolynomial index) point.1 *
          evaluationMap 11 (p11LogicalPolynomial index) point.1) =
        ∑ coordinate : Fin 2,
          evaluationMap 11 (p11LogicalPolynomial index)
              (p11SelectedPunctureEquivFin.symm coordinate).1 *
            evaluationMap 11 (p11LogicalPolynomial index)
              (p11SelectedPunctureEquivFin.symm coordinate).1 *
              evaluationMap 11 (p11LogicalPolynomial index)
                (p11SelectedPunctureEquivFin.symm coordinate).1 :=
      Fintype.sum_equiv p11SelectedPunctureEquivFin _ _ (fun point => by simp)
    _ = -1 := by
      fin_cases index <;>
        simp [p11SelectedPunctureEquivFin, p11LogicalPolynomial, evaluationMap,
          Fin.sum_univ_succ]
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
theorem _root_.solution (index : Fin 2) : p11CubicRowFamily.epsilon index = 1 := by
  change cubicPairing 11 (p11LogicalRow index) (p11LogicalRow index)
    (p11LogicalRow index) = 1
  have hsplit := p11_retained_cubic_add_selected_cubic_eq_full
    (evaluationMap 11 (p11LogicalPolynomial index))
    (evaluationMap 11 (p11LogicalPolynomial index))
    (evaluationMap 11 (p11LogicalPolynomial index))
  have hfullLogical : cubicPairing 11
      (evaluationMap 11 (p11LogicalPolynomial index))
      (evaluationMap 11 (p11LogicalPolynomial index))
      (evaluationMap 11 (p11LogicalPolynomial index)) = 0 := by
    simpa only [Sum.elim_inl] using
      (p11_full_cubic_zero (Sum.inl index) (Sum.inl index) (Sum.inl index))
  have hselected := p11_logical_selected_cube_sum index
  change cubicPairing 11 (restrictKept 11 2 (evaluationMap 11 (p11LogicalPolynomial index)))
    (restrictKept 11 2 (evaluationMap 11 (p11LogicalPolynomial index)))
    (restrictKept 11 2 (evaluationMap 11 (p11LogicalPolynomial index))) = 1
  rw [hselected, hfullLogical] at hsplit
  linear_combination hsplit
end QEC.Distillation.KT19P11ReedSolomonCubicBridge
