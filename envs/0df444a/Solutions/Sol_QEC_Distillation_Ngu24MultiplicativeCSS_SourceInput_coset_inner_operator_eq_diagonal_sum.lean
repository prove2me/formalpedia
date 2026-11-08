-- Prove2me | solution 1 for QEC.Distillation.Ngu24MultiplicativeCSS.SourceInput.coset_inner_operator_eq_diagonal_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T12:33:50.212593+00:00
-- url     : https://prove2.me/submissions/5fa27494-3ed0-4354-a91e-f7a3226a2778

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
    (hsep : ∀ u v h k,
      (∀ j, j ∉ S → data.shortenedCosetLabel u h j = data.shortenedCosetLabel v k j) →
        u = v ∧ h = k)
    (hlocal : ∀ x y : Word F data.PivotComplement,
      (∃ j, j ∉ S ∧ x j ≠ y j) →
        inner Complex (registerBasisKet x) (E (registerBasisKet y)) = 0)
    (u : Word F Logical) :
    inner Complex (data.shortenedCosetKet u) (E (data.shortenedCosetKet u)) =
      star (cosetNormalization data.H0) * cosetNormalization data.H0 *
        ∑ h : data.H0, inner Complex (registerBasisKet (data.shortenedCosetLabel u h))
          (E (registerBasisKet (data.shortenedCosetLabel u h))) := by
  unfold shortenedCosetKet
  rw [map_smul, map_sum, inner_smul_left, inner_smul_right, inner_sum, ← mul_assoc]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [sum_inner]
  apply Finset.sum_eq_single k
  · intro h _ hne
    apply hlocal
    by_contra! hbad
    exact hne (hsep u u h k hbad).2
  · simp
end QEC.Distillation.Ngu24MultiplicativeCSS.SourceInput
