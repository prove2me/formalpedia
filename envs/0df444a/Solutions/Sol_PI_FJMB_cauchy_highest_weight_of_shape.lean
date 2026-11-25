-- Prove2me | solution 1 for PI.FJMB.cauchy_highest_weight_of_shape
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:39:43.674358+00:00
-- url     : https://prove2.me/submissions/596f37b0-8a45-4d4a-8291-b7314125fbf1

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_PurCauchy
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_BlockDegreeAntitone
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_CauchyHighestWeightOfShape
import Theorems.Thm_PI_FJMB_cauchyHW_of
import Theorems.Thm_PI_FJMF_block_degree_antitone


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.FJMB
namespace PI.FJMB
theorem _root_.solution (hS : HypShape) (hD : HypDiag) (hF : HypFree) : PI.FJM.CauchyHW := by
  refine cauchyHW_of ?_ hS hD hF
  intro σ m n ι hι α P hP hrow hdeg
  exact PI.FJMF.block_degree_antitone σ m n ι hι α P hP hrow hdeg
end PI.FJMB
