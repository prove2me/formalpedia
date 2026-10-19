-- Prove2me | solution 1 for PermanentRollout.squareFreeMonomial_eq_monomial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:07.661825+00:00
-- url     : https://prove2.me/submissions/260d7738-06bb-40a1-9226-3ed1454419a8

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
namespace PermanentRollout
theorem _root_.solution {ι : Type*} (rows : Finset ι) :
    squareFreeMonomial rows =
      MvPolynomial.monomial (squareFreeExponent rows) (1 : ℂ) := by
  classical
  simpa [squareFreeMonomial, squareFreeExponent] using
    (MvPolynomial.prod_X_pow (R := ℂ) (fun _ : ι => 1) rows)
end PermanentRollout
