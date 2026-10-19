-- Prove2me | solution 1 for PermanentFormulaLowerBound.permanentPolynomial_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:11.481307+00:00
-- url     : https://prove2.me/submissions/6e711962-75e3-4f01-9640-7269d496f008

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentFormulaLowerBound
universe u v w
open scoped BigOperators Kronecker Matrix IntermediateField.algebraAdjoinAdjoin
namespace PermanentFormulaLowerBound
theorem _root_.solution (n : ℕ) :
    permanentPolynomial n =
      ∑ σ : Equiv.Perm (Fin n),
        ∏ i : Fin n, MvPolynomial.X (i, σ i) := by
  classical
  unfold permanentPolynomial
  rw [← Matrix.permanent_transpose]
  rfl
end PermanentFormulaLowerBound
