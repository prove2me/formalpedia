-- Prove2me | solution 1 for TunnellMap.triplePolynomial_primitivePartTriple
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:06:11.21085+00:00
-- url     : https://prove2.me/submissions/0bcb610b-422f-4082-b0a6-2a77cfa8021b

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
import Theorems.Thm_TunnellMap_triplePolynomial_natDegree_le_two
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

set_option autoImplicit true
open TunnellMap
open Polynomial
namespace TunnellMap
theorem _root_.solution (v : Triple) :
    triplePolynomial (primitivePartTriple v) = (triplePolynomial v).primPart := by
  apply Polynomial.ext
  intro n
  by_cases hn : n ≤ 2
  · interval_cases n <;> simp [primitivePartTriple, polynomialTriple]
  · have hnLarge : 2 < n := Nat.lt_of_not_ge hn
    have hleftDeg : (triplePolynomial (primitivePartTriple v)).natDegree ≤ 2 :=
      triplePolynomial_natDegree_le_two _
    have hrightDeg : (triplePolynomial v).primPart.natDegree ≤ 2 := by
      rw [Polynomial.natDegree_primPart]
      exact triplePolynomial_natDegree_le_two _
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt
      (lt_of_le_of_lt hleftDeg hnLarge)]
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt
      (lt_of_le_of_lt hrightDeg hnLarge)]
end TunnellMap
