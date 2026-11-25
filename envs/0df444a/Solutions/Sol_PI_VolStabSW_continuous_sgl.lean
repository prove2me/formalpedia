-- Prove2me | solution 1 for PI.VolStabSW.continuous_sgl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:54:36.129387+00:00
-- url     : https://prove2.me/submissions/19d3b43c-8400-41e8-8f37-b00a6b8822a2

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
theorem _root_.solution {F : Type} [Field F] (v : InfinitePlace F) : Continuous (sgl v) :=
  continuous_single v
end PI.VolStabSW
