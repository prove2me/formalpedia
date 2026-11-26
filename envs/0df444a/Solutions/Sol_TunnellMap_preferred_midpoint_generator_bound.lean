-- Prove2me | solution 1 for TunnellMap.preferred_midpoint_generator_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:41:45.916302+00:00
-- url     : https://prove2.me/submissions/52c1f009-be73-4bef-a380-c2bc4e3c893d

import Definitions.Def_TunnellMap_ProjectiveKey
import Definitions.Def_TunnellMap_MidpointBound
import Theorems.Thm_TunnellMap_qForm_vsmul
import Theorems.Thm_TunnellMap_plusVector_eq_two_vsmul_of_halfSum
import Theorems.Thm_TunnellMap_minusVector_eq_two_vsmul_of_halfDiff
import Theorems.Thm_TunnellMap_qForm_halfSum_add_halfDiff
import Theorems.Thm_TunnellMap_DirectionKey_form_le_of_le
import Theorems.Thm_TunnellMap_GloballyRanked_insertEquiv_at_left
import Theorems.Thm_TunnellMap_GloballyRanked_insertEquiv_symm_at_right
import Theorems.Thm_TunnellMap_directionKey_negTriple
import Theorems.Thm_TunnellMap_directionKey_primitiveDirection
import Theorems.Thm_TunnellMap_directionScale_ne_zero
import Theorems.Thm_TunnellMap_direction_decomposition
import Theorems.Thm_TunnellMap_dot_tau
import Theorems.Thm_TunnellMap_evenEquiv_apply
import Theorems.Thm_TunnellMap_evenEquiv_symm_apply
import Theorems.Thm_TunnellMap_midpoint_parity
import Theorems.Thm_TunnellMap_minusVector_ne_zero
import Theorems.Thm_TunnellMap_minusVector_neg_source
import Theorems.Thm_TunnellMap_minusVector_neg_target
import Theorems.Thm_TunnellMap_odd_third_ne_zero
import Theorems.Thm_TunnellMap_plusVector_ne_zero
import Theorems.Thm_TunnellMap_plusVector_neg_source
import Theorems.Thm_TunnellMap_plusVector_neg_target
import Theorems.Thm_TunnellMap_plus_minus_keys_ne
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
import Theorems.Thm_TunnellMap_qForm_pos_of_ne_zero
import Theorems.Thm_TunnellMap_qForm_tau
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


attribute [local simp] TunnellMap.qForm_vsmul

set_option autoImplicit true
open TunnellMap
namespace TunnellMap
theorem _root_.solution {n : ℤ} (hn : Odd n)
    (s : BResidual n) (t : AResidual n) :
    2 * qForm (primitiveDirection (preferredVector s t)) ≤ n - 1 := by
  obtain ⟨hPlus, hMinus, hPlusEq, hPlusOdd, hMinusEq, hMinusOdd⟩ :=
    midpoint_parity hn s.1 t.1
  have hPlusNe : hPlus ≠ ⟨0, 0, 0⟩ := odd_third_ne_zero hPlusOdd
  have hMinusNe : hMinus ≠ ⟨0, 0, 0⟩ := odd_third_ne_zero hMinusOdd
  have hRawPlus := plusVector_eq_two_vsmul_of_halfSum s t hPlus hPlusEq
  have hRawMinus := minusVector_eq_two_vsmul_of_halfDiff s t hMinus hMinusEq
  have hDirPlus : primitiveDirection (plusVector s t) = primitiveDirection hPlus := by
    rw [hRawPlus, primitiveDirection_two_vsmul hPlusNe]
  have hDirMinus : primitiveDirection (minusVector s t) = primitiveDirection hMinus := by
    rw [hRawMinus, primitiveDirection_two_vsmul hMinusNe]
  let a := directionScale hPlus
  let b := directionScale hMinus
  let d := primitiveDirection (plusVector s t)
  let e := primitiveDirection (minusVector s t)
  have hDecPlus : hPlus = vsmul a d := by
    rw [direction_decomposition hPlus, ← hDirPlus]
  have hDecMinus : hMinus = vsmul b e := by
    rw [direction_decomposition hMinus, ← hDirMinus]
  have ha : a ≠ 0 := directionScale_ne_zero hPlusNe
  have hb : b ≠ 0 := directionScale_ne_zero hMinusNe
  have hd : d ≠ ⟨0, 0, 0⟩ := primitiveDirection_ne_zero (plusVector_ne_zero s t)
  have he : e ≠ ⟨0, 0, 0⟩ := primitiveDirection_ne_zero (minusVector_ne_zero s t)
  have hNormSum := qForm_halfSum_add_halfDiff s t hPlus hMinus hPlusEq hMinusEq
  have hNormPlus : qForm hPlus = a ^ 2 * qForm d := by
    rw [hDecPlus, qForm_vsmul]
  have hNormMinus : qForm hMinus = b ^ 2 * qForm e := by
    rw [hDecMinus, qForm_vsmul]
  have haSq : 1 ≤ a ^ 2 := sq_pos_of_ne_zero ha
  have hbSq : 1 ≤ b ^ 2 := sq_pos_of_ne_zero hb
  have hdPos : 0 < qForm d := qForm_pos_of_ne_zero hd
  have hePos : 0 < qForm e := qForm_pos_of_ne_zero he
  have hLowerPlus : qForm d ≤ qForm hPlus := by
    rw [hNormPlus]
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right haSq (le_of_lt hdPos)
  have hLowerMinus : qForm e ≤ qForm hMinus := by
    rw [hNormMinus]
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hbSq (le_of_lt hePos)
  have hLowerSum : qForm d + qForm e ≤ n := by
    calc
      qForm d + qForm e ≤ qForm hPlus + qForm hMinus :=
        add_le_add hLowerPlus hLowerMinus
      _ = n := hNormSum
  obtain ⟨k, hk⟩ := hn
  have boundPlus (hde : qForm d ≤ qForm e) : 2 * qForm d ≤ n - 1 := by
    omega
  have boundMinus (hed : qForm e ≤ qForm d) : 2 * qForm e ≤ n - 1 := by
    omega
  by_cases hlt : directionKey (plusVector s t) < directionKey (minusVector s t)
  · have hde : qForm d ≤ qForm e := by
      have hfirst := DirectionKey.form_le_of_le hlt.le
      simpa [directionKey, d, e] using hfirst
    simpa [preferredVector, hlt, d] using boundPlus hde
  · have hrev : directionKey (minusVector s t) < directionKey (plusVector s t) :=
      lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm (plus_minus_keys_ne s t))
    have hed : qForm e ≤ qForm d := by
      have hfirst := DirectionKey.form_le_of_le hrev.le
      simpa [directionKey, d, e] using hfirst
    simpa [preferredVector, hlt, e] using boundMinus hed
end TunnellMap
