-- Prove2me | solution 1 for PI.WickFormula.Gen.gdelta_dL_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:01:35.214216+00:00
-- url     : https://prove2.me/submissions/a58a2218-1b4e-4563-b3f7-147db5c28265

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
variable {K I J : Type} [CommRing K] [Fintype I] [Fintype J]
namespace PI.WickFormula.Gen
theorem _root_.solution (κ : I → J → K) (i : I) (S : MvPolynomial (I ⊕ J) K) :
    gdelta κ (dL κ i S) = dL κ i (gdelta κ S) :=
  LinearMap.congr_fun (commute_gdelta_dL κ i).eq S
end PI.WickFormula.Gen
