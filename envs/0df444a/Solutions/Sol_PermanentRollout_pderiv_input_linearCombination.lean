-- Prove2me | solution 1 for PermanentRollout.pderiv_input_linearCombination
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:05.100639+00:00
-- url     : https://prove2.me/submissions/3e3d94ab-e561-4f67-be39-9f272c6c6907

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_pderiv_linearCombination

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
noncomputable section
open scoped BigOperators
namespace PermanentRollout
theorem _root_.solution {ι : Type*} (input : ι)
    (coefficients : ι →₀ ℂ) :
    MvPolynomial.pderiv input
        (Finsupp.linearCombination ℂ MvPolynomial.X coefficients) =
      MvPolynomial.C (coefficients input) := by
  classical
  rw [pderiv_linearCombination]
  by_cases hinput : coefficients input = 0
  · simp [Finsupp.linearCombination_apply, Finsupp.sum,
      MvPolynomial.pderiv_X, Pi.single_apply, hinput,
      Finsupp.mem_support_iff]
  · simp [Finsupp.linearCombination_apply, Finsupp.sum,
      MvPolynomial.pderiv_X, Pi.single_apply, hinput,
      Finsupp.mem_support_iff, MvPolynomial.smul_eq_C_mul]
end PermanentRollout
