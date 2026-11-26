-- Prove2me | solution 1 for TunnellMap.fixed_endpoint_line_unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:37:55.931155+00:00
-- url     : https://prove2.me/submissions/2cc33d19-0ba1-48a2-802f-3324e0d0f16e

import Definitions.Def_TunnellMap_PrimitiveDirection
import Definitions.Def_TunnellMap_GloballyRankedExistence
import Definitions.Def_TunnellMap_ProjectiveKey
import Theorems.Thm_TunnellMap_qForm_pos_of_ne_zero
import Theorems.Thm_TunnellMap_directionKey_negTriple
import Theorems.Thm_TunnellMap_directionKey_primitiveDirection
import Theorems.Thm_TunnellMap_plusVector_neg_source
import Theorems.Thm_TunnellMap_minusVector_neg_source
import Theorems.Thm_TunnellMap_plusVector_neg_target
import Theorems.Thm_TunnellMap_minusVector_neg_target
import Theorems.Thm_TunnellMap_representativeEdgeKey_neg_source
import Theorems.Thm_TunnellMap_representativeEdgeKey_neg_target
import Theorems.Thm_TunnellMap_endpoint_scale_equation
import Theorems.Thm_TunnellMap_GloballyRanked_insertEquiv_at_left
import Theorems.Thm_TunnellMap_GloballyRanked_insertEquiv_symm_at_right
import Theorems.Thm_TunnellMap_dot_tau
import Theorems.Thm_TunnellMap_evenEquiv_apply
import Theorems.Thm_TunnellMap_evenEquiv_symm_apply
import Theorems.Thm_TunnellMap_polynomialTriple_neg
import Theorems.Thm_TunnellMap_polynomialTriple_triplePolynomial
import Theorems.Thm_TunnellMap_primitiveDirection_idem
import Theorems.Thm_TunnellMap_primitiveDirection_negTriple
import Theorems.Thm_TunnellMap_primitiveDirection_two_vsmul
import Theorems.Thm_TunnellMap_primitivePartTriple_negTriple
import Theorems.Thm_TunnellMap_primitivePartTriple_two_vsmul
import Theorems.Thm_TunnellMap_qForm_aLift
import Theorems.Thm_TunnellMap_qForm_bLift
import Theorems.Thm_TunnellMap_qForm_tau
import Theorems.Thm_TunnellMap_tripleContent_negTriple
import Theorems.Thm_TunnellMap_tripleContent_orientDirection
import Theorems.Thm_TunnellMap_tripleContent_primitiveDirection
import Theorems.Thm_TunnellMap_tripleContent_primitivePartTriple
import Theorems.Thm_TunnellMap_triplePolynomial_coeff_one
import Theorems.Thm_TunnellMap_triplePolynomial_coeff_two
import Theorems.Thm_TunnellMap_triplePolynomial_coeff_zero
import Theorems.Thm_TunnellMap_triplePolynomial_negTriple
import Theorems.Thm_TunnellMap_triplePolynomial_vsmul
attribute [local simp] TunnellMap.GloballyRanked.insertEquiv_at_left
attribute [local simp] TunnellMap.GloballyRanked.insertEquiv_symm_at_right
attribute [local simp] TunnellMap.dot_tau
attribute [local simp] TunnellMap.evenEquiv_apply
attribute [local simp] TunnellMap.evenEquiv_symm_apply
attribute [local simp] TunnellMap.polynomialTriple_neg
attribute [local simp] TunnellMap.polynomialTriple_triplePolynomial
attribute [local simp] TunnellMap.primitiveDirection_idem
attribute [local simp] TunnellMap.primitiveDirection_negTriple
attribute [local simp] TunnellMap.primitiveDirection_two_vsmul
attribute [local simp] TunnellMap.primitivePartTriple_negTriple
attribute [local simp] TunnellMap.primitivePartTriple_two_vsmul
attribute [local simp] TunnellMap.qForm_aLift
attribute [local simp] TunnellMap.qForm_bLift
attribute [local simp] TunnellMap.qForm_tau
attribute [local simp] TunnellMap.tripleContent_negTriple
attribute [local simp] TunnellMap.tripleContent_orientDirection
attribute [local simp] TunnellMap.tripleContent_primitiveDirection
attribute [local simp] TunnellMap.tripleContent_primitivePartTriple
attribute [local simp] TunnellMap.triplePolynomial_coeff_one
attribute [local simp] TunnellMap.triplePolynomial_coeff_two
attribute [local simp] TunnellMap.triplePolynomial_coeff_zero
attribute [local simp] TunnellMap.triplePolynomial_negTriple
attribute [local simp] TunnellMap.triplePolynomial_vsmul


attribute [local simp] TunnellMap.directionKey_negTriple
attribute [local simp] TunnellMap.directionKey_primitiveDirection
attribute [local simp] TunnellMap.plusVector_neg_source
attribute [local simp] TunnellMap.minusVector_neg_source
attribute [local simp] TunnellMap.plusVector_neg_target
attribute [local simp] TunnellMap.minusVector_neg_target
attribute [local simp] TunnellMap.representativeEdgeKey_neg_source
attribute [local simp] TunnellMap.representativeEdgeKey_neg_target

set_option autoImplicit true
open TunnellMap
namespace TunnellMap
theorem _root_.solution {E F₁ F₂ d : Triple} {a b : ℤ}
    (hnorm₁ : qForm F₁ = qForm E) (hnorm₂ : qForm F₂ = qForm E)
    (hd : d ≠ ⟨0, 0, 0⟩) (ha : a ≠ 0) (hb : b ≠ 0)
    (hline₁ : vadd E F₁ = vsmul a d ∨ vsub E F₁ = vsmul a d)
    (hline₂ : vadd E F₂ = vsmul b d ∨ vsub E F₂ = vsmul b d) :
    F₂ = F₁ ∨ F₂ = negTriple F₁ := by
  have haeq := endpoint_scale_equation hnorm₁ ha hline₁
  have hbeq := endpoint_scale_equation hnorm₂ hb hline₂
  have hq : qForm d ≠ 0 := ne_of_gt (qForm_pos_of_ne_zero hd)
  have hab : a = b := by
    apply mul_right_cancel₀ hq
    exact haeq.trans hbeq.symm
  subst b
  rcases hline₁ with hplus₁ | hminus₁ <;>
    rcases hline₂ with hplus₂ | hminus₂
  · left
    apply Triple.ext
    · have h₁ := congrArg Triple.x hplus₁
      have h₂ := congrArg Triple.x hplus₂
      simp [vadd, vsmul] at h₁ h₂
      linarith
    · have h₁ := congrArg Triple.y hplus₁
      have h₂ := congrArg Triple.y hplus₂
      simp [vadd, vsmul] at h₁ h₂
      linarith
    · have h₁ := congrArg Triple.z hplus₁
      have h₂ := congrArg Triple.z hplus₂
      simp [vadd, vsmul] at h₁ h₂
      linarith
  · right
    apply Triple.ext
    · have h₁ := congrArg Triple.x hplus₁
      have h₂ := congrArg Triple.x hminus₂
      simp [vadd, vsub, vsmul, negTriple] at h₁ h₂ ⊢
      linarith
    · have h₁ := congrArg Triple.y hplus₁
      have h₂ := congrArg Triple.y hminus₂
      simp [vadd, vsub, vsmul, negTriple] at h₁ h₂ ⊢
      linarith
    · have h₁ := congrArg Triple.z hplus₁
      have h₂ := congrArg Triple.z hminus₂
      simp [vadd, vsub, vsmul, negTriple] at h₁ h₂ ⊢
      linarith
  · right
    apply Triple.ext
    · have h₁ := congrArg Triple.x hminus₁
      have h₂ := congrArg Triple.x hplus₂
      simp [vadd, vsub, vsmul, negTriple] at h₁ h₂ ⊢
      linarith
    · have h₁ := congrArg Triple.y hminus₁
      have h₂ := congrArg Triple.y hplus₂
      simp [vadd, vsub, vsmul, negTriple] at h₁ h₂ ⊢
      linarith
    · have h₁ := congrArg Triple.z hminus₁
      have h₂ := congrArg Triple.z hplus₂
      simp [vadd, vsub, vsmul, negTriple] at h₁ h₂ ⊢
      linarith
  · left
    apply Triple.ext
    · have h₁ := congrArg Triple.x hminus₁
      have h₂ := congrArg Triple.x hminus₂
      simp [vsub, vsmul] at h₁ h₂
      linarith
    · have h₁ := congrArg Triple.y hminus₁
      have h₂ := congrArg Triple.y hminus₂
      simp [vsub, vsmul] at h₁ h₂
      linarith
    · have h₁ := congrArg Triple.z hminus₁
      have h₂ := congrArg Triple.z hminus₂
      simp [vsub, vsmul] at h₁ h₂
      linarith
end TunnellMap
