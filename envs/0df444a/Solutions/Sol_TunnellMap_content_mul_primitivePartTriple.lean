-- Prove2me | solution 1 for TunnellMap.content_mul_primitivePartTriple
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:12:41.076387+00:00
-- url     : https://prove2.me/submissions/ea644d02-74f1-40f5-aa8c-68167eefc555

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
import Theorems.Thm_TunnellMap_primitivePartTriple_negTriple
import Theorems.Thm_TunnellMap_primitivePartTriple_two_vsmul
import Theorems.Thm_TunnellMap_tripleContent_primitivePartTriple
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
attribute [local simp] TunnellMap.primitivePartTriple_negTriple
attribute [local simp] TunnellMap.primitivePartTriple_two_vsmul
attribute [local simp] TunnellMap.tripleContent_primitivePartTriple

set_option autoImplicit true
open TunnellMap
open Polynomial
namespace TunnellMap
theorem _root_.solution (v : Triple) :
    v = vsmul (tripleContent v) (primitivePartTriple v) := by
  apply Triple.ext
  · have h := congrArg (fun f : ℤ[X] => f.coeff 0)
      (Polynomial.eq_C_content_mul_primPart (triplePolynomial v))
    simpa [tripleContent, primitivePartTriple, polynomialTriple, vsmul] using h
  · have h := congrArg (fun f : ℤ[X] => f.coeff 1)
      (Polynomial.eq_C_content_mul_primPart (triplePolynomial v))
    simpa [tripleContent, primitivePartTriple, polynomialTriple, vsmul] using h
  · have h := congrArg (fun f : ℤ[X] => f.coeff 2)
      (Polynomial.eq_C_content_mul_primPart (triplePolynomial v))
    simpa [tripleContent, primitivePartTriple, polynomialTriple, vsmul] using h
end TunnellMap
