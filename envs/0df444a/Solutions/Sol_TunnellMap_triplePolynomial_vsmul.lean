-- Prove2me | solution 1 for TunnellMap.triplePolynomial_vsmul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:03:27.575478+00:00
-- url     : https://prove2.me/submissions/861acc74-21ed-4d81-9779-0e461dafb813

import Definitions.Def_TunnellMap_AffineLattice
import Definitions.Def_TunnellMap_Antipodal
import Definitions.Def_TunnellMap_PrimitiveDirection
import Theorems.Thm_TunnellMap_polynomialTriple_neg
import Theorems.Thm_TunnellMap_triplePolynomial_coeff_zero
import Theorems.Thm_TunnellMap_triplePolynomial_coeff_one
import Theorems.Thm_TunnellMap_triplePolynomial_coeff_two
import Theorems.Thm_TunnellMap_polynomialTriple_triplePolynomial
import Theorems.Thm_TunnellMap_triplePolynomial_negTriple
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

set_option autoImplicit true
open TunnellMap
open Polynomial
namespace TunnellMap
theorem _root_.solution (a : ℤ) (v : Triple) :
    triplePolynomial (vsmul a v) = C a * triplePolynomial v := by
  simp [triplePolynomial, vsmul]
  ring
end TunnellMap
