-- Prove2me | solution 1 for PI.VolStabW.FiniteThetaCoordinates.continuous_piW_inf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:57:11.676854+00:00
-- url     : https://prove2.me/submissions/3afa254a-3be5-4b5b-9757-ca8d8e520d3d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_VolStabFromSWW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_FinTheta

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW PI.VolStabW.FiniteThetaCoordinates
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain
open scoped TensorProduct
variable (F : Type) [Field F] [NumberField F]
namespace PI.VolStabW.FiniteThetaCoordinates
theorem _root_.solution (w : InfinitePlace F) :
    Continuous (Pi.evalAlgHom F (fun w : InfinitePlace F => w.Completion) w : Ainf F → w.Completion) :=
  continuous_apply w
end PI.VolStabW.FiniteThetaCoordinates
