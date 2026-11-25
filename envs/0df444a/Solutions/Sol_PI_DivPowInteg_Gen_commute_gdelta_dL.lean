-- Prove2me | solution 1 for PI.DivPowInteg.Gen.commute_gdelta_dL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:46:31.704851+00:00
-- url     : https://prove2.me/submissions/173abfe0-dc5c-46a4-98d8-27e5f3825e1f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_DividedPowerIntegrals_GenDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_DividedPowerIntegrals_GenPow
import Theorems.Thm_PI_DivPowInteg_Gen_commute_gdelta_pd
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
private theorem gdelta_pderiv_comm (κ : I → J → K) (c : I ⊕ J) (S : MvPolynomial (I ⊕ J) K) :
    gdelta κ (pderiv c S) = pderiv c (gdelta κ S) :=
  LinearMap.congr_fun (commute_gdelta_pd κ c).eq S
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
theorem _root_.solution (κ : I → J → K) (i : I) : Commute (gdelta κ) (dL κ i) := by
  refine LinearMap.ext fun S => ?_
  show gdelta κ (dL κ i S) = dL κ i (gdelta κ S)
  rw [dL_apply', dL_apply', map_sum]
  simp only [map_smul, gdelta_pderiv_comm]
end PI.DivPowInteg.Gen
