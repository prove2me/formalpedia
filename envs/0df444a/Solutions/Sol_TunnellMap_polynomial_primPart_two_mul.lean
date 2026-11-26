-- Prove2me | solution 1 for TunnellMap.polynomial_primPart_two_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:09:19.243155+00:00
-- url     : https://prove2.me/submissions/40ed08c7-374d-4fb9-a560-f79c2bc129df

import Definitions.Def_TunnellMap_AffineLattice
import Definitions.Def_TunnellMap_Antipodal
import Definitions.Def_TunnellMap_PrimitiveDirection
import Theorems.Thm_TunnellMap_polynomialTriple_neg
import Theorems.Thm_TunnellMap_triplePolynomial_coeff_zero
import Theorems.Thm_TunnellMap_triplePolynomial_coeff_one
import Theorems.Thm_TunnellMap_triplePolynomial_coeff_two
import Theorems.Thm_TunnellMap_polynomialTriple_triplePolynomial
import Theorems.Thm_TunnellMap_triplePolynomial_negTriple
import Theorems.Thm_TunnellMap_triplePolynomial_vsmul
import Theorems.Thm_TunnellMap_tripleContent_negTriple
import Theorems.Thm_TunnellMap_dot_tau
import Theorems.Thm_TunnellMap_evenEquiv_apply
import Theorems.Thm_TunnellMap_evenEquiv_symm_apply
import Theorems.Thm_TunnellMap_qForm_aLift
import Theorems.Thm_TunnellMap_qForm_bLift
import Theorems.Thm_TunnellMap_qForm_tau
attribute [local simp] TunnellMap.dot_tau
attribute [local simp] TunnellMap.evenEquiv_apply
attribute [local simp] TunnellMap.evenEquiv_symm_apply
attribute [local simp] TunnellMap.qForm_aLift
attribute [local simp] TunnellMap.qForm_bLift
attribute [local simp] TunnellMap.qForm_tau


attribute [local simp] TunnellMap.polynomialTriple_neg
attribute [local simp] TunnellMap.triplePolynomial_coeff_zero
attribute [local simp] TunnellMap.triplePolynomial_coeff_one
attribute [local simp] TunnellMap.triplePolynomial_coeff_two
attribute [local simp] TunnellMap.polynomialTriple_triplePolynomial
attribute [local simp] TunnellMap.triplePolynomial_negTriple
attribute [local simp] TunnellMap.triplePolynomial_vsmul
attribute [local simp] TunnellMap.tripleContent_negTriple

set_option autoImplicit true
open TunnellMap
open Polynomial
namespace TunnellMap
theorem _root_.solution {f : ℤ[X]} (hf : f ≠ 0) :
    (C (2 : ℤ) * f).primPart = f.primPart := by
  have hc : f.content ≠ 0 := by
    intro h
    exact hf (Polynomial.content_eq_zero_iff.mp h)
  have hcontent : (C (2 : ℤ) * f).content = 2 * f.content := by
    rw [Polynomial.content_C_mul, ← Int.abs_eq_normalize]
    norm_num
  have hbase := Polynomial.eq_C_content_mul_primPart f
  have hscaled := Polynomial.eq_C_content_mul_primPart (C (2 : ℤ) * f)
  rw [hcontent] at hscaled
  apply mul_left_cancel₀ (show C (2 * f.content) ≠ (0 : ℤ[X]) by
    simp [hc])
  calc
    C (2 * f.content) * (C (2 : ℤ) * f).primPart = C (2 : ℤ) * f :=
      hscaled.symm
    _ = C (2 : ℤ) * (C f.content * f.primPart) := by rw [← hbase]
    _ = C (2 * f.content) * f.primPart := by simp [mul_assoc]
end TunnellMap
