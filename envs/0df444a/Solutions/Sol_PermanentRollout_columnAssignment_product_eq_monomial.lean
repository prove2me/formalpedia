-- Prove2me | solution 1 for PermanentRollout.columnAssignment_product_eq_monomial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:07.661825+00:00
-- url     : https://prove2.me/submissions/e408f964-c598-4f87-b297-30566a1c9f4e

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
namespace PermanentRollout
theorem _root_.solution {r k : ℕ}
    (U : Matrix (Fin r) (Fin k) ℂ) (assignment : Fin k → Fin r) :
    (∏ column : Fin k,
      MvPolynomial.C (U (assignment column) column) *
        MvPolynomial.X (assignment column)) =
      MvPolynomial.monomial (columnAssignmentExponent assignment)
        (∏ column : Fin k, U (assignment column) column) := by
  classical
  simpa [columnAssignmentExponent,
    MvPolynomial.C_mul_X_eq_monomial] using
    (MvPolynomial.monomial_sum_prod
      (R := ℂ) (Finset.univ : Finset (Fin k))
      (fun column => Finsupp.single (assignment column) 1)
      (fun column => U (assignment column) column)).symm
end PermanentRollout
