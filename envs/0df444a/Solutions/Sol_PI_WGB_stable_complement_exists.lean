-- Prove2me | solution 1 for PI.WGB.stable_complement_exists
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:54:29.964177+00:00
-- url     : https://prove2.me/submissions/abf0176b-dcde-42e7-9049-5d9f9d5e34cc

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_ExtremalFacts
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_RenameTauHomogB
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_ConstructionB
import Theorems.Thm_PI_WGB_stableCompl_B


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WGB
open Formalism.BasicNotions MvPolynomial
namespace PI.WGB
theorem _root_.solution : StableCompl := stableCompl_B
end PI.WGB
