-- Prove2me | solution 1 for TunnellMap.endpoint_scale_equation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:35:53.69889+00:00
-- url     : https://prove2.me/submissions/93013fd5-875c-4b19-b91f-b186aaeeaf65

import Definitions.Def_TunnellMap_PrimitiveDirection
import Definitions.Def_TunnellMap_GloballyRankedExistence
import Definitions.Def_TunnellMap_ProjectiveKey
import Theorems.Thm_TunnellMap_directionKey_negTriple
import Theorems.Thm_TunnellMap_directionKey_primitiveDirection
import Theorems.Thm_TunnellMap_plusVector_neg_source
import Theorems.Thm_TunnellMap_minusVector_neg_source
import Theorems.Thm_TunnellMap_plusVector_neg_target
import Theorems.Thm_TunnellMap_minusVector_neg_target
import Theorems.Thm_TunnellMap_representativeEdgeKey_neg_source
import Theorems.Thm_TunnellMap_representativeEdgeKey_neg_target
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
theorem _root_.solution {E F d : Triple} {a : ℤ}
    (hnorm : qForm F = qForm E) (ha : a ≠ 0)
    (hline : vadd E F = vsmul a d ∨ vsub E F = vsmul a d) :
    a * qForm d = 2 * qBilinear E d := by
  have hfactor : a * (a * qForm d - 2 * qBilinear E d) = 0 := by
    rcases hline with hplus | hminus
    · have hx := congrArg Triple.x hplus
      have hy := congrArg Triple.y hplus
      have hz := congrArg Triple.z hplus
      simp [vadd, vsmul] at hx hy hz
      have hfx : F.x = a * d.x - E.x := by linarith
      have hfy : F.y = a * d.y - E.y := by linarith
      have hfz : F.z = a * d.z - E.z := by linarith
      simp [qForm] at hnorm
      rw [hfx, hfy, hfz] at hnorm
      change a * (a * (2 * d.x ^ 2 + d.y ^ 2 + 2 * d.z ^ 2) -
        2 * (2 * E.x * d.x + E.y * d.y + 2 * E.z * d.z)) = 0
      ring_nf at hnorm ⊢
      linear_combination hnorm
    · have hx := congrArg Triple.x hminus
      have hy := congrArg Triple.y hminus
      have hz := congrArg Triple.z hminus
      simp [vsub, vsmul] at hx hy hz
      have hfx : F.x = E.x - a * d.x := by linarith
      have hfy : F.y = E.y - a * d.y := by linarith
      have hfz : F.z = E.z - a * d.z := by linarith
      simp [qForm] at hnorm
      rw [hfx, hfy, hfz] at hnorm
      change a * (a * (2 * d.x ^ 2 + d.y ^ 2 + 2 * d.z ^ 2) -
        2 * (2 * E.x * d.x + E.y * d.y + 2 * E.z * d.z)) = 0
      ring_nf at hnorm ⊢
      linear_combination hnorm
  have hzero := (mul_eq_zero.mp hfactor).resolve_left ha
  linarith
end TunnellMap
