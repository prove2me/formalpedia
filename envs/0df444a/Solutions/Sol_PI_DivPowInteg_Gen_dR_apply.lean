-- Prove2me | solution 1 for PI.DivPowInteg.Gen.dR_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:35:17.671246+00:00
-- url     : https://prove2.me/submissions/1125e620-fe49-4f74-b79c-7679693b4718

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
private theorem dR_apply' (κ : I → J → K) (j : J) (R : MvPolynomial (I ⊕ J) K) :
    dR κ j R = ∑ i, κ i j • pderiv (Sum.inl i) R := by
  simp [dR]
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
theorem _root_.solution (κ : I → J → K) (j : J) (R : MvPolynomial (I ⊕ J) K) :
    dR κ j R = ∑ i, κ i j • pderiv (Sum.inl i) R := by
  exact dR_apply' κ j R
end PI.DivPowInteg.Gen
