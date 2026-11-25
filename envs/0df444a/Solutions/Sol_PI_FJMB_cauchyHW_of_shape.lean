-- Prove2me | solution 1 for PI.FJMB.cauchyHW_of_shape
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:44:35.114084+00:00
-- url     : https://prove2.me/submissions/06c55d83-b4dc-434e-8a85-bae7edf9e05c

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_CauchyHighestWeightOfShape
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_DiagonalImageBlockFree
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_CauchyHWOfShape
import Theorems.Thm_PI_FJMB_cauchy_highest_weight_of_shape
import Theorems.Thm_PI_FJMB_diagonal_hypothesis
import Theorems.Thm_PI_FJMB_diagonal_image_block_free


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
theorem _root_.solution (hS : HypShape) : PI.FJM.CauchyHW :=
  cauchy_highest_weight_of_shape hS diagonal_hypothesis diagonal_image_block_free
end PI.FJMB
