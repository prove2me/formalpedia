-- Prove2me | solution 1 for PI.VolStabS.fFCount_of_inert
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:39:27.777933+00:00
-- url     : https://prove2.me/submissions/9e537ca3-7c80-4fe0-a723-ce05d3bcdb89

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_LocDensFFS
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_LocDensFFT
import Theorems.Thm_PI_VolStabS_fFCount_of
import Theorems.Thm_PI_VolStabS_fFSplit_holds


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabS
namespace PI.VolStabS
theorem _root_.solution (hI : FFInert) : FFCount := fFCount_of fFSplit_holds hI
end PI.VolStabS
