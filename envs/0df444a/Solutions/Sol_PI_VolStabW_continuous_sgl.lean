-- Prove2me | solution 1 for PI.VolStabW.continuous_sgl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:59:38.108025+00:00
-- url     : https://prove2.me/submissions/f9aaea36-93d7-4650-a905-8dbdead83394

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensSAChar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensChLift

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
open PI PI.VolStabW
open Classical
namespace PI.VolStabW
theorem _root_.solution {F : Type} [Field F] (v : InfinitePlace F) : Continuous (sgl v) :=
  continuous_single (A := fun w : InfinitePlace F => w.Completion) v
end PI.VolStabW
