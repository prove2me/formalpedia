-- Prove2me | solution 1 for TunnellMap.representativeEdgeKey_source_orbit_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:39:04.458842+00:00
-- url     : https://prove2.me/submissions/1558a1a6-8491-4ceb-a3e7-f4f6844f4502

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
import Theorems.Thm_TunnellMap_residualTargetLift_injective
import Theorems.Thm_TunnellMap_residualTargetLift_neg
import Theorems.Thm_TunnellMap_residualSourceLift_neg
import Theorems.Thm_TunnellMap_GloballyRanked_insertEquiv_at_left
import Theorems.Thm_TunnellMap_GloballyRanked_insertEquiv_symm_at_right
import Theorems.Thm_TunnellMap_directionScale_ne_zero
import Theorems.Thm_TunnellMap_direction_decomposition
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
    (hnpos : 0 < n) (s : BResidual n) {t₁ t₂ : AResidual n}
    (hkey : representativeEdgeKey s t₁ = representativeEdgeKey s t₂) :
    (aResidualInvolution n hnpos).orbit t₁ =
      (aResidualInvolution n hnpos).orbit t₂ := by
  rw [representativeEdgeKey_eq_preferred, representativeEdgeKey_eq_preferred] at hkey
  have hdir : primitiveDirection (preferredVector s t₁) =
      primitiveDirection (preferredVector s t₂) := directionKey_eq_iff.mp hkey
  let d := primitiveDirection (preferredVector s t₁)
  let a := directionScale (preferredVector s t₁)
  let b := directionScale (preferredVector s t₂)
  have hp₁ := preferredVector_eq_plus_or_minus s t₁
  have hp₂ := preferredVector_eq_plus_or_minus s t₂
  have hdec₁ : preferredVector s t₁ = vsmul a d := direction_decomposition _
  have hdec₂ : preferredVector s t₂ = vsmul b d := by
    have h := direction_decomposition (preferredVector s t₂)
    rw [← hdir] at h
    exact h
  have hline₁ : plusVector s t₁ = vsmul a d ∨ minusVector s t₁ = vsmul a d :=
    hp₁.elim (fun h => Or.inl (h.symm.trans hdec₁))
      (fun h => Or.inr (h.symm.trans hdec₁))
  have hline₂ : plusVector s t₂ = vsmul b d ∨ minusVector s t₂ = vsmul b d :=
    hp₂.elim (fun h => Or.inl (h.symm.trans hdec₂))
      (fun h => Or.inr (h.symm.trans hdec₂))
  have ha : a ≠ 0 := directionScale_ne_zero (by
    rcases hp₁ with h | h
    · rw [h]; exact plusVector_ne_zero s t₁
    · rw [h]; exact minusVector_ne_zero s t₁)
  have hb : b ≠ 0 := directionScale_ne_zero (by
    rcases hp₂ with h | h
    · rw [h]; exact plusVector_ne_zero s t₂
    · rw [h]; exact minusVector_ne_zero s t₂)
  have hd : d ≠ ⟨0, 0, 0⟩ := primitiveDirection_ne_zero (by
    rcases preferredVector_eq_plus_or_minus s t₁ with h | h
    · rw [h]; exact plusVector_ne_zero s t₁
    · rw [h]; exact minusVector_ne_zero s t₁)
  have hnorm₁ : qForm (residualTargetLift t₁) = qForm (residualSourceLift s) := by
    simp [residualTargetLift, residualSourceLift]
  have hnorm₂ : qForm (residualTargetLift t₂) = qForm (residualSourceLift s) := by
    simp [residualTargetLift, residualSourceLift]
  have horbit := fixed_endpoint_line_unique hnorm₁ hnorm₂ hd ha hb hline₁ hline₂
  let AI := aResidualInvolution n hnpos
  rcases horbit with hsame | hneg
  · have : t₂ = t₁ := residualTargetLift_injective hsame
    subst t₂
    rfl
  · have : t₂ = negAResidual t₁ := by
      apply residualTargetLift_injective
      simpa using hneg
    rw [this]
    exact (AI.orbit_neg t₁).symm
end TunnellMap
