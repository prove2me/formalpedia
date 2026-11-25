-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UsCost.commLR
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:03:58.282252+00:00
-- url     : https://prove2.me/submissions/553f00cb-457c-481a-8b8c-36a8b590458f

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_LetterSize
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_RightRegularActionListDLREqAppend
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_GrothendieckCommutativity_rightRegularAction_list_dLR_eq_append

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.BetaSesquilinearity
open scoped ContDiff
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UsCost
namespace PI.UnitaryGroupMassFormula.UsCost
theorem _root_.solution : CommLR := by
  unfold CommLR
  intro k r E _ _ f m hf u v w hu hv hw hlen g hg
  exact GrothendieckCommutativity.rightRegularAction_list_dLR_eq_append hf u v hu hv w hw hlen g hg
end PI.UnitaryGroupMassFormula.UsCost
