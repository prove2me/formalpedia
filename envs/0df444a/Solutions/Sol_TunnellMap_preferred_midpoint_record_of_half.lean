-- Prove2me | solution 1 for TunnellMap.preferred_midpoint_record_of_half
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:17:45.742399+00:00
-- url     : https://prove2.me/submissions/f408a064-7f7b-44e9-9d94-df58e88ac983

import Definitions.Def_TunnellMap_OrbitLift
import Definitions.Def_TunnellMap_MidpointBound
import Definitions.Def_TunnellMap_MidpointRecord
import Theorems.Thm_TunnellMap_vadd_eq_two_vsmul_of_halfSum
import Theorems.Thm_TunnellMap_GloballyRanked_insertEquiv_at_left
import Theorems.Thm_TunnellMap_GloballyRanked_insertEquiv_symm_at_right
import Theorems.Thm_TunnellMap_assemble_inl
import Theorems.Thm_TunnellMap_assemble_inr
import Theorems.Thm_TunnellMap_directionKey_negTriple
import Theorems.Thm_TunnellMap_directionKey_primitiveDirection
import Theorems.Thm_TunnellMap_directionScale_ne_zero
import Theorems.Thm_TunnellMap_direction_decomposition
import Theorems.Thm_TunnellMap_dot_tau
import Theorems.Thm_TunnellMap_endpoint_scale_equation
import Theorems.Thm_TunnellMap_evenEquiv_apply
import Theorems.Thm_TunnellMap_evenEquiv_symm_apply
import Theorems.Thm_TunnellMap_minusVector_neg_source
import Theorems.Thm_TunnellMap_minusVector_neg_target
import Theorems.Thm_TunnellMap_odd_third_ne_zero
import Theorems.Thm_TunnellMap_orientDirection_firstNonzeroPositive
import Theorems.Thm_TunnellMap_plusVector_neg_source
import Theorems.Thm_TunnellMap_plusVector_neg_target
import Theorems.Thm_TunnellMap_polynomialTriple_neg
import Theorems.Thm_TunnellMap_polynomialTriple_triplePolynomial
import Theorems.Thm_TunnellMap_preferred_midpoint_generator_bound
import Theorems.Thm_TunnellMap_primitiveDirection_idem
import Theorems.Thm_TunnellMap_primitiveDirection_negTriple
import Theorems.Thm_TunnellMap_primitiveDirection_two_vsmul
import Theorems.Thm_TunnellMap_primitivePartTriple_ne_zero
import Theorems.Thm_TunnellMap_primitivePartTriple_negTriple
import Theorems.Thm_TunnellMap_primitivePartTriple_two_vsmul
import Theorems.Thm_TunnellMap_qForm_aLift
import Theorems.Thm_TunnellMap_qForm_bLift
import Theorems.Thm_TunnellMap_qForm_tau
import Theorems.Thm_TunnellMap_qForm_vsmul
import Theorems.Thm_TunnellMap_representativeEdgeKey_neg_source
import Theorems.Thm_TunnellMap_representativeEdgeKey_neg_target
import Theorems.Thm_TunnellMap_residualSourceLift_neg
import Theorems.Thm_TunnellMap_residualTargetLift_neg
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
attribute [local simp] TunnellMap.assemble_inl
attribute [local simp] TunnellMap.assemble_inr
attribute [local simp] TunnellMap.directionKey_negTriple
attribute [local simp] TunnellMap.directionKey_primitiveDirection
attribute [local simp] TunnellMap.dot_tau
attribute [local simp] TunnellMap.evenEquiv_apply
attribute [local simp] TunnellMap.evenEquiv_symm_apply
attribute [local simp] TunnellMap.minusVector_neg_source
attribute [local simp] TunnellMap.minusVector_neg_target
attribute [local simp] TunnellMap.plusVector_neg_source
attribute [local simp] TunnellMap.plusVector_neg_target
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
attribute [local simp] TunnellMap.qForm_vsmul
attribute [local simp] TunnellMap.representativeEdgeKey_neg_source
attribute [local simp] TunnellMap.representativeEdgeKey_neg_target
attribute [local simp] TunnellMap.residualSourceLift_neg
attribute [local simp] TunnellMap.residualTargetLift_neg
attribute [local simp] TunnellMap.tripleContent_negTriple
attribute [local simp] TunnellMap.tripleContent_orientDirection
attribute [local simp] TunnellMap.tripleContent_primitiveDirection
attribute [local simp] TunnellMap.tripleContent_primitivePartTriple
attribute [local simp] TunnellMap.triplePolynomial_coeff_one
attribute [local simp] TunnellMap.triplePolynomial_coeff_two
attribute [local simp] TunnellMap.triplePolynomial_coeff_zero
attribute [local simp] TunnellMap.triplePolynomial_negTriple
attribute [local simp] TunnellMap.triplePolynomial_vsmul



set_option autoImplicit true
open TunnellMap
namespace TunnellMap
theorem _root_.solution {n : ℤ} (hn : Odd n)
    (s : BResidual n) (t target : AResidual n) (htarget : target = preferredTarget s t)
    (h : Triple) (hodd : Odd h.z)
    (hhalf : IsHalfSum h (residualSourceLift s) (residualTargetLift target))
    (hpref : preferredVector s t = vsmul 2 h) :
    Nonempty (PreferredMidpointRecord s t) := by
  have hne : h ≠ ⟨0, 0, 0⟩ := odd_third_ne_zero hodd
  let d := primitiveDirection h
  let q := directionScale h
  have hdec : h = vsmul q d := direction_decomposition h
  have hdir : d = primitiveDirection (preferredVector s t) := by
    rw [hpref, primitiveDirection_two_vsmul hne]
  have hqne : q ≠ 0 := directionScale_ne_zero hne
  have hzprod : h.z = q * d.z := congrArg Triple.z hdec
  have hprodOdd : Odd (q * d.z) := by
    rw [← hzprod]
    exact hodd
  have hqodd : Odd q := (Int.odd_mul.mp hprodOdd).1
  have hdodd : Odd d.z := (Int.odd_mul.mp hprodOdd).2
  have hfirst : FirstNonzeroPositive d := by
    exact orientDirection_firstNonzeroPositive (primitivePartTriple_ne_zero hne)
  have hline : vadd (residualSourceLift s) (residualTargetLift target) =
      vsmul (2 * q) d := by
    calc
      vadd (residualSourceLift s) (residualTargetLift target) = vsmul 2 h :=
        vadd_eq_two_vsmul_of_halfSum hhalf
      _ = vsmul 2 (vsmul q d) := by rw [hdec]
      _ = vsmul (2 * q) d := by ext <;> simp [vsmul] <;> ring
  have hnorm : qForm (residualTargetLift target) = qForm (residualSourceLift s) := by
    simp [residualTargetLift, residualSourceLift]
  have hscale := endpoint_scale_equation hnorm (mul_ne_zero (by norm_num) hqne)
    (Or.inl hline)
  have hbilinear : qBilinear (residualSourceLift s) d = q * qForm d := by
    nlinarith
  have htargetFormula : residualTargetLift target =
      vadd (negTriple (residualSourceLift s)) (vsmul (2 * q) d) := by
    apply Triple.ext
    · have hx := congrArg Triple.x hline
      simp [vadd, vsmul, negTriple] at hx ⊢
      linarith
    · have hy := congrArg Triple.y hline
      simp [vadd, vsmul, negTriple] at hy ⊢
      linarith
    · have hz := congrArg Triple.z hline
      simp [vadd, vsmul, negTriple] at hz ⊢
      linarith
  have hbound := preferred_midpoint_generator_bound hn s t
  refine ⟨{
    target := target
    target_eq := htarget
    half := h
    half_odd := hodd
    half_sum := hhalf
    direction := d
    multiplier := q
    direction_eq := hdir
    half_decomposition := hdec
    multiplier_odd := hqodd
    direction_third_odd := hdodd
    direction_oriented := hfirst
    bilinear := hbilinear
    target_formula := htargetFormula
    direction_bound := ?_ }⟩
  simpa [hdir] using hbound
end TunnellMap
