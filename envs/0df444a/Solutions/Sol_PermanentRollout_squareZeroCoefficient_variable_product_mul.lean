-- Prove2me | solution 1 for PermanentRollout.squareZeroCoefficient_variable_product_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:09.567922+00:00
-- url     : https://prove2.me/submissions/684a6a0f-16b8-4fd0-95c3-8a30b84f9dcc

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_squareFreeMonomial_quotient_eq_variable_product
import Theorems.Thm_PermanentRollout_coeff_squareFreeMonomial_mul

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
namespace PermanentRollout
theorem _root_.solution (r : ℕ)
    (target removed : Finset (Fin r)) (p : SquareZeroAlgebra r) :
    squareZeroCoefficient r target
      ((∏ i ∈ removed, squareZeroVariable r i) * p) =
        if removed ⊆ target then
          squareZeroCoefficient r (target \ removed) p
        else 0 := by
  classical
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective p
  rw [← squareFreeMonomial_quotient_eq_variable_product,
    ← map_mul, squareZeroCoefficient_mk,
    coeff_squareFreeMonomial_mul]
  split_ifs <;> simp [squareZeroCoefficient_mk]
end PermanentRollout
