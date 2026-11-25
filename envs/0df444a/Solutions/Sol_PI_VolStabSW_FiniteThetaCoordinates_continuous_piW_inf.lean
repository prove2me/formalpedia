-- Prove2me | solution 1 for PI.VolStabSW.FiniteThetaCoordinates.continuous_piW_inf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:01:08.346701+00:00
-- url     : https://prove2.me/submissions/7fe8163d-9ccd-4db5-a818-15a023ccb2b3

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_FibInfEx
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_FinTheta

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabSW PI.VolStabSW.FiniteThetaCoordinates
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain
open scoped TensorProduct
variable (F : Type) [Field F] [NumberField F]
namespace PI.VolStabSW.FiniteThetaCoordinates
theorem _root_.solution (w : InfinitePlace F) :
    Continuous (Pi.evalAlgHom F (fun w : InfinitePlace F => w.Completion) w : Ainf F → w.Completion) :=
  continuous_apply w
end PI.VolStabSW.FiniteThetaCoordinates
