-- Prove2me | solution 1 for PI.DivPowInteg.Gen.gdelta_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:41:33.412833+00:00
-- url     : https://prove2.me/submissions/98546825-49ce-4a2e-9764-2980402891b2

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
private theorem gdelta_apply' (κ : I → J → K) (R : MvPolynomial (I ⊕ J) K) :
    gdelta κ R = ∑ i, ∑ j, κ i j • pderiv (Sum.inl i) (pderiv (Sum.inr j) R) := by
  simp [gdelta]
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
theorem _root_.solution (κ : I → J → K) (R : MvPolynomial (I ⊕ J) K) :
    gdelta κ R = ∑ i, ∑ j, κ i j • pderiv (Sum.inl i) (pderiv (Sum.inr j) R) := by
  exact gdelta_apply' κ R
end PI.DivPowInteg.Gen
