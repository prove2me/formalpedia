-- Prove2me | solution 1 for PI.VolStabSW.sgl_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:55:58.927036+00:00
-- url     : https://prove2.me/submissions/88f190ec-ee4d-4dd3-a645-6d57e0f2de82

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensSAChar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensChLift

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Complex
open PI PI.VolStabSW
open Classical
namespace PI.VolStabSW
theorem _root_.solution {F : Type} [Field F] (v : InfinitePlace F) : sgl v (0 : v.Completion) = 0 :=
  Pi.single_zero v
end PI.VolStabSW
