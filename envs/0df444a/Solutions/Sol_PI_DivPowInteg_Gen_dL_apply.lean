-- Prove2me | solution 1 for PI.DivPowInteg.Gen.dL_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:27:22.609026+00:00
-- url     : https://prove2.me/submissions/4946f2ee-f71e-4f4b-a3f9-5c34ffca9f66

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_DividedPowerIntegrals_GenDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_DividedPowerIntegrals_GenPow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open MvPolynomial
namespace PI.DivPowInteg.Gen
section
variable {K I J : Type} [CommRing K] [Fintype I] [Fintype J]
private theorem dL_apply' (κ : I → J → K) (i : I) (R : MvPolynomial (I ⊕ J) K) :
    dL κ i R = ∑ j, κ i j • pderiv (Sum.inr j) R := by
  simp [dL]
end
section
variable {K I J : Type} [CommRing K] [Algebra ℚ K] [Fintype I] [Fintype J]
end
end PI.DivPowInteg.Gen
end

set_option autoImplicit false
open MvPolynomial
open PI PI.DivPowInteg PI.DivPowInteg.Gen
variable {K I J : Type} [CommRing K] [Fintype I] [Fintype J]
namespace PI.DivPowInteg.Gen
theorem _root_.solution (κ : I → J → K) (i : I) (R : MvPolynomial (I ⊕ J) K) :
    dL κ i R = ∑ j, κ i j • pderiv (Sum.inr j) R := by
  exact dL_apply' κ i R
end PI.DivPowInteg.Gen
