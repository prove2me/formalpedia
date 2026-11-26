-- Prove2me | solution 1 for TunnellMap.representativeEdgeKey_target_orbit_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:40:50.3438+00:00
-- url     : https://prove2.me/submissions/20e694a9-9322-4eb6-9e99-0d52fd6c60ed

import Definitions.Def_TunnellMap_PrimitiveDirection
import Definitions.Def_TunnellMap_GloballyRankedExistence
import Definitions.Def_TunnellMap_ProjectiveKey
import Theorems.Thm_TunnellMap_directionKey_eq_iff
import Theorems.Thm_TunnellMap_directionKey_negTriple
import Theorems.Thm_TunnellMap_plusVector_ne_zero
import Theorems.Thm_TunnellMap_minusVector_ne_zero
import Theorems.Thm_TunnellMap_preferredVector_eq_plus_or_minus
import Theorems.Thm_TunnellMap_directionKey_primitiveDirection
import Theorems.Thm_TunnellMap_representativeEdgeKey_eq_preferred
import Theorems.Thm_TunnellMap_plusVector_neg_source
import Theorems.Thm_TunnellMap_minusVector_neg_source
import Theorems.Thm_TunnellMap_plusVector_neg_target
import Theorems.Thm_TunnellMap_minusVector_neg_target
import Theorems.Thm_TunnellMap_representativeEdgeKey_neg_source
import Theorems.Thm_TunnellMap_representativeEdgeKey_neg_target
import Theorems.Thm_TunnellMap_fixed_endpoint_line_unique
import Theorems.Thm_TunnellMap_residualTargetLift_neg
import Theorems.Thm_TunnellMap_residualSourceLift_injective
import Theorems.Thm_TunnellMap_residualSourceLift_neg
import Theorems.Thm_TunnellMap_preferred_fixed_target_line
import Theorems.Thm_TunnellMap_GloballyRanked_insertEquiv_at_left
import Theorems.Thm_TunnellMap_GloballyRanked_insertEquiv_symm_at_right
import Theorems.Thm_TunnellMap_dot_tau
import Theorems.Thm_TunnellMap_evenEquiv_apply
import Theorems.Thm_TunnellMap_evenEquiv_symm_apply
import Theorems.Thm_TunnellMap_polynomialTriple_neg
import Theorems.Thm_TunnellMap_polynomialTriple_triplePolynomial
import Theorems.Thm_TunnellMap_primitiveDirection_idem
import Theorems.Thm_TunnellMap_primitiveDirection_ne_zero
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
attribute [local simp] TunnellMap.residualTargetLift_neg
attribute [local simp] TunnellMap.residualSourceLift_neg

set_option autoImplicit true
open TunnellMap
namespace TunnellMap
theorem _root_.solution {n : ℤ}
    (t : AResidual n) {s₁ s₂ : BResidual n}
    (hkey : representativeEdgeKey s₁ t = representativeEdgeKey s₂ t) :
    (bResidualInvolution n).orbit s₁ = (bResidualInvolution n).orbit s₂ := by
  rw [representativeEdgeKey_eq_preferred, representativeEdgeKey_eq_preferred] at hkey
  have hdir : primitiveDirection (preferredVector s₁ t) =
      primitiveDirection (preferredVector s₂ t) := directionKey_eq_iff.mp hkey
  obtain ⟨a, ha, hline₁⟩ := preferred_fixed_target_line s₁ t
  obtain ⟨b, hb, hline₂⟩ := preferred_fixed_target_line s₂ t
  rw [← hdir] at hline₂
  have hd : primitiveDirection (preferredVector s₁ t) ≠ ⟨0, 0, 0⟩ :=
    primitiveDirection_ne_zero (by
      rcases preferredVector_eq_plus_or_minus s₁ t with h | h
      · rw [h]; exact plusVector_ne_zero s₁ t
      · rw [h]; exact minusVector_ne_zero s₁ t)
  have hnorm₁ : qForm (residualSourceLift s₁) = qForm (residualTargetLift t) := by
    simp [residualSourceLift, residualTargetLift]
  have hnorm₂ : qForm (residualSourceLift s₂) = qForm (residualTargetLift t) := by
    simp [residualSourceLift, residualTargetLift]
  have horbit := fixed_endpoint_line_unique hnorm₁ hnorm₂ hd ha hb hline₁ hline₂
  let BI := bResidualInvolution n
  rcases horbit with hsame | hneg
  · have : s₂ = s₁ := residualSourceLift_injective hsame
    subst s₂
    rfl
  · have : s₂ = negBResidual s₁ := by
      apply residualSourceLift_injective
      simpa using hneg
    rw [this]
    exact (BI.orbit_neg s₁).symm
end TunnellMap
