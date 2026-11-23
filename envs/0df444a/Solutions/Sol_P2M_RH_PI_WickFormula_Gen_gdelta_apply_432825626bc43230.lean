-- Prove2me | solution 1 for P2M_RH_PI_WickFormula_Gen_gdelta_apply_432825626bc43230
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:01:57.856102+00:00
-- url     : https://prove2.me/submissions/dd06a910-119a-4f18-87b1-dec35ad18a31

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_WickFormula_GenDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_WickFormula_GenVan

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open PI PI.WickFormula PI.WickFormula.Gen
variable {K I J : Type} [CommRing K] [Fintype I] [Fintype J]
namespace PI.WickFormula.Gen
theorem _root_.solution (κ : I → J → K) (R : MvPolynomial (I ⊕ J) K) :
    gdelta κ R = ∑ i, ∑ j, κ i j • pderiv (Sum.inl i) (pderiv (Sum.inr j) R) := by
  unfold gdelta
  simp [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply]
end PI.WickFormula.Gen
