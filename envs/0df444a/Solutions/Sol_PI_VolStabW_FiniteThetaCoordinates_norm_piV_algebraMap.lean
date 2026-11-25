-- Prove2me | solution 1 for PI.VolStabW.FiniteThetaCoordinates.norm_piV_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:57:06.086807+00:00
-- url     : https://prove2.me/submissions/5b156004-74cf-4d0f-9dfe-03906614e8a5

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
theorem _root_.solution (v : HeightOneSpectrum (𝓞 F)) (x : F) :
    ‖piV F v (algebraMap F (AF F) x)‖ = ‖FinitePlace.embedding v x‖ := by
  rw [AlgHom.commutes]
  rfl
end PI.VolStabW.FiniteThetaCoordinates
