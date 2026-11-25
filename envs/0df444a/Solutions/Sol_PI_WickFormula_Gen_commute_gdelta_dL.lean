-- Prove2me | solution 1 for PI.WickFormula.Gen.commute_gdelta_dL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:50:38.903123+00:00
-- url     : https://prove2.me/submissions/0fdd6533-7d4e-4754-8fca-5f8de45ce380

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_WickFormula_GenDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_WickFormula_GenPow
import Theorems.Thm_PI_WickFormula_Gen_commute_gdelta_pd

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
theorem _root_.solution (κ : I → J → K) (i : I) : Commute (gdelta κ) (dL κ i) := by
  unfold dL
  refine Commute.sum_right _ _ _ fun j _ => ?_
  exact Commute.smul_right (commute_gdelta_pd κ (Sum.inr j)) _
end PI.WickFormula.Gen
