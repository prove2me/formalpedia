-- Prove2me | solution 1 for PI.VolStabSW.sgl_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:55:55.732434+00:00
-- url     : https://prove2.me/submissions/cee47122-aa88-4395-96a2-6ed437368a4a

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
theorem _root_.solution {F : Type} [Field F] (v : InfinitePlace F) (x y : v.Completion) :
    sgl v (x + y) = sgl v x + sgl v y :=
  Pi.single_add v x y
end PI.VolStabSW
