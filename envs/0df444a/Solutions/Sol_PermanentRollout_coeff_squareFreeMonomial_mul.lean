-- Prove2me | solution 1 for PermanentRollout.coeff_squareFreeMonomial_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:09.567922+00:00
-- url     : https://prove2.me/submissions/498bcf2c-310f-4d80-847d-8c829186de9f

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_squareFreeMonomial_eq_monomial
import Theorems.Thm_PermanentRollout_squareFreeExponent_le_iff
import Theorems.Thm_PermanentRollout_squareFreeExponent_sub

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
namespace PermanentRollout
theorem _root_.solution {ι : Type*} [DecidableEq ι]
    (target removed : Finset ι) (p : MvPolynomial ι ℂ) :
    MvPolynomial.coeff (squareFreeExponent target)
      (squareFreeMonomial removed * p) =
        if removed ⊆ target then
          MvPolynomial.coeff (squareFreeExponent (target \ removed)) p
        else 0 := by
  classical
  rw [squareFreeMonomial_eq_monomial,
    MvPolynomial.coeff_monomial_mul']
  simp [squareFreeExponent_le_iff, squareFreeExponent_sub]
end PermanentRollout
