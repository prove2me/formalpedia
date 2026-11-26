-- Prove2me | solution 1 for TunnellMap.primitivePartTriple_two_vsmul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:10:33.147208+00:00
-- url     : https://prove2.me/submissions/8bd80ced-c6bd-42f5-b173-e9736e6316de

import Definitions.Def_TunnellMap_AffineLattice
import Definitions.Def_TunnellMap_Antipodal
import Definitions.Def_TunnellMap_PrimitiveDirection
import Theorems.Thm_TunnellMap_triplePolynomial_vsmul
import Theorems.Thm_TunnellMap_triplePolynomial_ne_zero
import Theorems.Thm_TunnellMap_polynomial_primPart_two_mul
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


attribute [local simp] TunnellMap.triplePolynomial_vsmul

set_option autoImplicit true
open TunnellMap
open Polynomial
namespace TunnellMap
theorem _root_.solution {v : Triple} (hv : v ≠ ⟨0, 0, 0⟩) :
    primitivePartTriple (vsmul 2 v) = primitivePartTriple v := by
  unfold primitivePartTriple
  rw [triplePolynomial_vsmul,
    polynomial_primPart_two_mul (triplePolynomial_ne_zero hv)]
end TunnellMap
