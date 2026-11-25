-- Prove2me | solution 1 for PI.VolStabS.continuous_sgl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:50:36.31233+00:00
-- url     : https://prove2.me/submissions/a94f63dc-071c-4c8c-b87d-e50ddb277de8

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_LocDensSAChar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_LocDensChLift

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
open PI PI.VolStabS
open Classical
namespace PI.VolStabS
theorem _root_.solution {F : Type} [Field F] (v : InfinitePlace F) : Continuous (sgl v) :=
  continuous_single (A := fun w : InfinitePlace F => w.Completion) v
end PI.VolStabS
