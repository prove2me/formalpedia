-- Prove2me | solution 1 for PI.WickFormula.Gen.commL_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:06:08.52917+00:00
-- url     : https://prove2.me/submissions/202ba618-f92d-4247-b9d7-a8a2f4103499

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_WickFormula_GenDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_WickFormula_GenPow
import Theorems.Thm_PI_WickFormula_Gen_commute_gdelta_dL

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
namespace PI.WickFormula.Gen
theorem _root_.solution : CommL := by
  intro K I J _ _ _ κ i R n
  have h := ((commute_gdelta_dL κ i).pow_left n).eq
  exact LinearMap.congr_fun h R
end PI.WickFormula.Gen
