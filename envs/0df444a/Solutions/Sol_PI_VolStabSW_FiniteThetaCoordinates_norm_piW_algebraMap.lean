-- Prove2me | solution 1 for PI.VolStabSW.FiniteThetaCoordinates.norm_piW_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:54:24.365445+00:00
-- url     : https://prove2.me/submissions/8d8e8268-244b-4f48-8d32-99418b3e4681

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
theorem _root_.solution (w : InfinitePlace F) (x : F) : ‖piW F w (algebraMap F (AF F) x)‖ = w x := by
  rw [AlgHom.commutes]
  exact InfinitePlace.Completion.norm_coe w _
end PI.VolStabSW.FiniteThetaCoordinates
