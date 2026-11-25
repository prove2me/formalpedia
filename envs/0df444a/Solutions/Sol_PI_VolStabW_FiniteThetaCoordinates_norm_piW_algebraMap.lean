-- Prove2me | solution 1 for PI.VolStabW.FiniteThetaCoordinates.norm_piW_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:57:08.439219+00:00
-- url     : https://prove2.me/submissions/27b574b7-6d92-469f-a8d8-c50a43b44c81

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
theorem _root_.solution (w : InfinitePlace F) (x : F) : ‖piW F w (algebraMap F (AF F) x)‖ = w x := by
  rw [AlgHom.commutes]
  exact InfinitePlace.Completion.norm_coe w _
end PI.VolStabW.FiniteThetaCoordinates
