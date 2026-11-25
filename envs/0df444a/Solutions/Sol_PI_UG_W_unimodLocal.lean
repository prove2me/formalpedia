-- Prove2me | solution 1 for PI.UG.W.unimodLocal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:46:29.410801+00:00
-- url     : https://prove2.me/submissions/1bf1f5f3-9943-4b15-8a8f-9a84fcbc78f5

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularGenus_StdLatEqSpan
import Definitions.Def_Formalism_HermitianLattices_StatementMass
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocDual
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularGenus_UnimodLocalOfLocDual
import Theorems.Thm_PI_UG_W_unimodLocal_of_locDual
import Theorems.Thm_Formalism_HermitianLatticesTheory_locDual


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
noncomputable section
open PI PI.UG PI.UG.W
namespace PI.UG.W
theorem _root_.solution : UnimodLocal := unimodLocal_of_locDual Formalism.HermitianLatticesTheory.locDual
end PI.UG.W
