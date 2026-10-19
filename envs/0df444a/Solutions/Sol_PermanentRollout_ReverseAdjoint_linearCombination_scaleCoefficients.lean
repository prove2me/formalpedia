-- Prove2me | solution 1 for PermanentRollout.ReverseAdjoint.linearCombination_scaleCoefficients
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:05.100639+00:00
-- url     : https://prove2.me/submissions/fab5cc2f-5964-4c9d-b15f-d97dae84d0cd

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
noncomputable section
open scoped BigOperators
open PermanentRollout.ReverseAdjoint
namespace PermanentRollout.ReverseAdjoint
theorem _root_.solution {ι κ : Type*}
    (adjoint : MvPolynomial ι ℂ) (coefficients : κ →₀ ℂ)
    (family : κ → MvPolynomial ι ℂ) :
    Finsupp.linearCombination (MvPolynomial ι ℂ) family
        (scaleCoefficients adjoint coefficients) =
      adjoint * Finsupp.linearCombination ℂ family coefficients := by
  classical
  simp only [Finsupp.linearCombination_apply, scaleCoefficients]
  rw [Finsupp.sum_mapRange_index
    (h := fun index coefficient => coefficient • family index)
    (fun _ => by simp)]
  simp [Finsupp.sum, Finset.mul_sum, MvPolynomial.smul_eq_C_mul,
    mul_assoc, mul_left_comm]
end PermanentRollout.ReverseAdjoint
