-- Prove2me | solution 1 for QEC.Distillation.Ngu24MultiplicativeCSS.SourceInput.detectableOn_of_coset_locality
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T12:37:15.816384+00:00
-- url     : https://prove2.me/submissions/2f4c87bd-0202-4b37-9f73-5892a23958fc

import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_CSSShortening
import Definitions.Def_QEC_Semantics_ErrorCorrection_Detectability
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_CosetDetectability
import Theorems.Thm_QEC_Distillation_Ngu24MultiplicativeCSS_SourceInput_coset_inner_operator_eq_zero
import Theorems.Thm_QEC_Distillation_Ngu24MultiplicativeCSS_SourceInput_coset_inner_operator_eq_diagonal_sum
import Theorems.Thm_QEC_Distillation_Ngu24MultiplicativeCSS_SourceInput_coset_diagonal_sum_eq_zero_label
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
    (honto : Function.Surjective (fun h : data.H0 =>
      fun j : S => data.puncture h.val.val j.val))
    (hlocal : ∀ x y : Word F data.PivotComplement,
      (∃ j, j ∉ S ∧ x j ≠ y j) →
        inner Complex (registerBasisKet x) (E (registerBasisKet y)) = 0)
    (hdiag : ∀ x y : Word F data.PivotComplement,
      (∀ j, j ∈ S → x j = y j) →
        inner Complex (registerBasisKet x) (E (registerBasisKet x)) =
          inner Complex (registerBasisKet y) (E (registerBasisKet y))) :
    DetectableOn data.quantumCode E := by
  let c := inner Complex (data.shortenedCosetKet 0) (E (data.shortenedCosetKet 0))
  have hmatrix (u v : Word F Logical) :
      inner Complex (data.shortenedCosetKet u) (E (data.shortenedCosetKet v)) =
        c * inner Complex (data.shortenedCosetKet u) (data.shortenedCosetKet v) := by
    by_cases huv : u = v
    · subst v
      rw [data.shortenedCosetKet_inner, if_pos rfl, mul_one]
      change _ = inner Complex (data.shortenedCosetKet 0) (E (data.shortenedCosetKet 0))
      rw [data.coset_inner_operator_eq_diagonal_sum E S hsep hlocal u,
        data.coset_inner_operator_eq_diagonal_sum E S hsep hlocal 0,
        data.coset_diagonal_sum_eq_zero_label E S honto hdiag u]
    · rw [data.coset_inner_operator_eq_zero E S hsep hlocal u v huv,
        data.shortenedCosetKet_inner, if_neg huv, mul_zero]
  refine ⟨c, ?_⟩
  rintro x ⟨psi, rfl⟩ y ⟨chi, rfl⟩
  change inner Complex
      (∑ u : Word F Logical, psi u • data.shortenedCosetKet u)
      (E (∑ v : Word F Logical, chi v • data.shortenedCosetKet v)) =
    c * inner Complex
      (∑ u : Word F Logical, psi u • data.shortenedCosetKet u)
      (∑ v : Word F Logical, chi v • data.shortenedCosetKet v)
  simp only [map_sum, map_smul, inner_sum, sum_inner, inner_smul_left, inner_smul_right]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro u _
  rw [hmatrix]
  ring
end QEC.Distillation.Ngu24MultiplicativeCSS.SourceInput
