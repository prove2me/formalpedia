-- Prove2me | solution 1 for PI.VolStabW.fFCount_of_inert
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:48:01.03108+00:00
-- url     : https://prove2.me/submissions/a65b98b0-24c7-44d2-96c5-c885e88d1115

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensFFS
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensFFT
import Theorems.Thm_PI_VolStabW_fFCount_of
import Theorems.Thm_PI_VolStabW_fFSplit_holds


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW
namespace PI.VolStabW
theorem _root_.solution (hI : FFInert) : FFCount := fFCount_of fFSplit_holds hI
end PI.VolStabW
