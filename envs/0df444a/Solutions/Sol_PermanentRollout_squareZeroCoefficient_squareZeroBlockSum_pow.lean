-- Prove2me | solution 1 for PermanentRollout.squareZeroCoefficient_squareZeroBlockSum_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:09.567922+00:00
-- url     : https://prove2.me/submissions/d728cb83-d92a-461a-a4a7-35cdeed314ba

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_squareFreeExponent_sum
import Theorems.Thm_PermanentRollout_squareFreeExponent_multinomial
import Theorems.Thm_PermanentRollout_squareFreeExponent_prod_treeBlockVector

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
namespace PermanentRollout
theorem _root_.solution (r : ℕ)
    (rows block : Finset (Fin r)) (degree : ℕ) :
    squareZeroCoefficient r rows (squareZeroBlockSum r block ^ degree) =
      if rows ⊆ block ∧ rows.card = degree then
        (degree.factorial : ℂ)
      else 0 := by
  classical
  have hblock :
      Ideal.Quotient.mk (squareZeroIdeal r)
          (∑ row : Fin r,
            treeBlockVector block row •
              (MvPolynomial.X row : MvPolynomial (Fin r) ℂ)) =
        squareZeroBlockSum r block := by
    simp [treeBlockVector, squareZeroBlockSum, squareZeroVariable]
  rw [← hblock, ← map_pow, squareZeroCoefficient_mk,
    MvPolynomial.coeff_linearCombination_X_pow_of_fintype,
    squareFreeExponent_sum, squareFreeExponent_multinomial,
    squareFreeExponent_prod_treeBlockVector]
  split_ifs with hcard hsubset hboth <;> simp_all
end PermanentRollout
