-- Prove2me | solution 1 for PermanentRollout.coeff_columnLinearFormProduct_eq_assignment_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:07.661825+00:00
-- url     : https://prove2.me/submissions/555bf25e-9b6a-49be-a688-0ef9e6ecad11

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_columnAssignment_product_eq_monomial

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
namespace PermanentRollout
theorem _root_.solution {r k : ℕ}
    (U : Matrix (Fin r) (Fin k) ℂ) (rows : Finset (Fin r)) :
    MvPolynomial.coeff (squareFreeExponent rows)
      (columnLinearFormProduct U) =
        ∑ assignment : Fin k → Fin r,
          if columnAssignmentExponent assignment = squareFreeExponent rows
          then ∏ column : Fin k, U (assignment column) column
          else 0 := by
  classical
  unfold columnLinearFormProduct columnLinearForm
  rw [Fintype.prod_sum]
  change (MvPolynomial.coeffAddMonoidHom (squareFreeExponent rows))
    (∑ assignment : Fin k → Fin r,
      ∏ column : Fin k,
        MvPolynomial.C (U (assignment column) column) *
          MvPolynomial.X (assignment column)) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro assignment _
  rw [columnAssignment_product_eq_monomial]
  change MvPolynomial.coeff (squareFreeExponent rows)
    (MvPolynomial.monomial (columnAssignmentExponent assignment)
      (∏ column : Fin k, U (assignment column) column)) = _
  rw [MvPolynomial.coeff_monomial]
end PermanentRollout
