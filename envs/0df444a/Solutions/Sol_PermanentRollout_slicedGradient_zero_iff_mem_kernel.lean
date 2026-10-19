-- Prove2me | solution 1 for PermanentRollout.slicedGradient_zero_iff_mem_kernel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:03.983104+00:00
-- url     : https://prove2.me/submissions/3193658a-72f3-4b85-a66d-2206ec4454f6

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_slicedGradientPolynomial_eval

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
noncomputable section
open scoped BigOperators LinearAlgebra.Projectivization
namespace PermanentRollout
theorem _root_.solution {m k : ℕ}
    (P : MvPolynomial (Fin m) ℂ)
    (W : (Fin k → ℂ) →ₗ[ℂ] (Fin m → ℂ))
    (A : (Fin m → ℂ) →ₗ[ℂ] (Fin k → ℂ))
    (u : Fin k → ℂ) :
    (∀ i, MvPolynomial.eval u (slicedGradientPolynomial P W A i) = 0) ↔
      gradientVector P (W u) ∈ LinearMap.ker A := by
  rw [LinearMap.mem_ker]
  simp [slicedGradientPolynomial_eval, funext_iff]
end PermanentRollout
