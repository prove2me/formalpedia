-- Prove2me | solution 1 for PI.WickFormula.Gen.commute_gdelta_pd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:42:15.437567+00:00
-- url     : https://prove2.me/submissions/71d3540d-bec3-408a-a7ae-11eb3acbe6f9

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_WickFormula_GenDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_WickFormula_GenPow
import Theorems.Thm_PI_WickFormula_Gen_commute_pd

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
theorem _root_.solution (κ : I → J → K) (c : I ⊕ J) : Commute (gdelta κ) (pd c) := by
  unfold gdelta
  refine Commute.sum_left _ _ _ fun i _ => Commute.sum_left _ _ _ fun j _ => ?_
  refine Commute.smul_left ?_ _
  exact (commute_pd (Sum.inl i) c).mul_left (commute_pd (Sum.inr j) c)
end PI.WickFormula.Gen
