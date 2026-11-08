-- Prove2me | solution 1 for QEC.Distillation.Ngu24MultiplicativeCSS.SourceInput.coset_diagonal_sum_eq_zero_label
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T12:35:01.635386+00:00
-- url     : https://prove2.me/submissions/308c77fb-24fd-40fc-af44-f8313e190969

import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_CSSShortening
import Definitions.Def_QEC_Semantics_ErrorCorrection_Detectability
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_CosetDetectability
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Distillation_assembleTagged_extractBlock
import Theorems.Thm_QEC_Distillation_extractBlock_assembleTagged
import Theorems.Thm_QEC_Distillation_mem_coordinateSupport
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Distillation.assembleTagged_extractBlock
attribute [local simp] QEC.Distillation.extractBlock_assembleTagged
attribute [local simp] QEC.Distillation.mem_coordinateSupport
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_apply
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_toOperator
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator



set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Ngu24MultiplicativeCSS QEC.Distillation.Ngu24MultiplicativeCSS.SourceInput
open Coding Semantics
open scoped BigOperators
universe u
variable {F I Logical : Type u} [Field F] [Fintype F] [Fintype I] [Fintype Logical]
attribute [local instance] QEC.Distillation.Ngu24MultiplicativeCSS.SourceInput._p2m_local_instance_b70f205f2b_23
attribute [local instance] QEC.Distillation.Ngu24MultiplicativeCSS.SourceInput._p2m_local_instance_b70f205f2b_24
attribute [local instance] QEC.Distillation.Ngu24MultiplicativeCSS.SourceInput._p2m_local_instance_b70f205f2b_25
namespace QEC.Distillation.Ngu24MultiplicativeCSS.SourceInput
theorem _root_.solution (data : SourceInput F I Logical)
    (E : Operator (ComputationalBasisRegister F data.PivotComplement))
    (S : Finset data.PivotComplement)
    (honto : Function.Surjective (fun h : data.H0 =>
      fun j : S => data.puncture h.val.val j.val))
    (hdiag : ∀ x y : Word F data.PivotComplement,
      (∀ j, j ∈ S → x j = y j) →
        inner Complex (registerBasisKet x) (E (registerBasisKet x)) =
          inner Complex (registerBasisKet y) (E (registerBasisKet y)))
    (u : Word F Logical) :
    (∑ h : data.H0, inner Complex (registerBasisKet (data.shortenedCosetLabel u h))
      (E (registerBasisKet (data.shortenedCosetLabel u h)))) =
    ∑ h : data.H0, inner Complex (registerBasisKet (data.shortenedCosetLabel 0 h))
      (E (registerBasisKet (data.shortenedCosetLabel 0 h))) := by
  obtain ⟨shift, hshift⟩ := honto (fun j => data.puncturedLogicalWord u j.val)
  apply Fintype.sum_equiv (Equiv.addRight shift)
  intro h
  apply hdiag
  intro j hj
  have hs := congrFun hshift ⟨j, hj⟩
  change data.puncture shift.val.val j = data.puncturedLogicalWord u j at hs
  change data.puncturedLogicalWord u j + data.puncture h.val.val j =
    data.puncturedLogicalWord 0 j + data.puncture (h + shift).val.val j
  have hz : data.puncturedLogicalWord 0 = 0 := by
    simp [puncturedLogicalWord, systematicLogicalWord]
  rw [hz]
  change data.puncturedLogicalWord u j + h.val.val j.val =
    0 + (h.val.val j.val + shift.val.val j.val)
  change shift.val.val j.val = data.puncturedLogicalWord u j at hs
  rw [hs]
  simp [add_comm]
end QEC.Distillation.Ngu24MultiplicativeCSS.SourceInput
