-- Prove2me | solution 1 for PI.DivPowInteg.Top.dpow_X_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:40:31.59282+00:00
-- url     : https://prove2.me/submissions/189c7058-bf16-4cdf-affe-4692f0e5279b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DivPowInteg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_DividedPowerIntegrals_GenDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_DividedPowerIntegrals_NatMulFactorialBound
import Theorems.Thm_PI_DivPowInteg_Top_nat_mul_factorial_bound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open PI PI.DivPowInteg PI.DivPowInteg.Top
open PI.DivPowInteg.Gen
variable {A K I J : Type} [CommRing A] [CommRing K] [Algebra ℚ K] [Algebra A K]
  [Fintype I] [Fintype J]
namespace PI.DivPowInteg.Top
theorem _root_.solution (κ : I → J → K) (s : I ⊕ J)
    (D : MvPolynomial (I ⊕ J) K →ₗ[K] MvPolynomial (I ⊕ J) K) (R : MvPolynomial (I ⊕ J) K)
    (k : ℕ)
    (h : (gdelta κ ^ (k + 1)) (X s * R) =
      X s * (gdelta κ ^ (k + 1)) R + (k + 1) • D ((gdelta κ ^ k) R)) :
    dpow κ (k + 1) (X s * R) = X s * dpow κ (k + 1) R + D (dpow κ k R) := by
  unfold dpow
  rw [h, smul_add, mul_smul_comm, ← Nat.cast_smul_eq_nsmul ℚ, smul_smul, nat_mul_factorial_bound,
    LinearMap.map_smul_of_tower]
end PI.DivPowInteg.Top
