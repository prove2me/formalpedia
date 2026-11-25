-- Prove2me | solution 1 for PI.WickFormula.Gen.commute_pd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:29:48.430797+00:00
-- url     : https://prove2.me/submissions/1a9c5587-4fb0-48bd-8f8c-cccd89533690

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_WickFormula_GenDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_WickFormula_GenPow
import Theorems.Thm_PI_WickFormula_Gen_pderiv_comm

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
theorem _root_.solution (a b : I ⊕ J) : Commute (pd (K := K) a) (pd b) := by
  apply LinearMap.ext
  intro p
  exact pderiv_comm a b p
end PI.WickFormula.Gen
