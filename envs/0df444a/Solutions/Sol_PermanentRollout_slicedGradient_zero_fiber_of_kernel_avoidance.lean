-- Prove2me | solution 1 for PermanentRollout.slicedGradient_zero_fiber_of_kernel_avoidance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:03.983104+00:00
-- url     : https://prove2.me/submissions/d6636cd9-355b-43a1-85cd-d4ae0f728192

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_slicedGradientPolynomial_eval_zero
import Theorems.Thm_PermanentRollout_slicedGradient_zero_iff_mem_kernel

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
noncomputable section
open scoped BigOperators LinearAlgebra.Projectivization
namespace PermanentRollout
theorem _root_.solution {m k d : ℕ}
    (P : MvPolynomial (Fin m) ℂ)
    (hd : 2 ≤ d) (hP : P.IsHomogeneous d)
    (W : (Fin k → ℂ) →ₗ[ℂ] (Fin m → ℂ))
    (A : (Fin m → ℂ) →ₗ[ℂ] (Fin k → ℂ))
    (havoid : ∀ u : Fin k → ℂ, u ≠ 0 →
      gradientVector P (W u) ∉ LinearMap.ker A) :
    ∀ u : Fin k → ℂ,
      (∀ i, MvPolynomial.eval u (slicedGradientPolynomial P W A i) = 0) ↔
        u = 0 := by
  intro u
  constructor
  · intro hzero
    by_contra hne
    exact havoid u hne
      ((slicedGradient_zero_iff_mem_kernel P W A u).mp hzero)
  · rintro rfl i
    exact slicedGradientPolynomial_eval_zero P hd hP W A i
end PermanentRollout
