-- Prove2me | solution 1 for PI.VolStabW.qV_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:02:46.483359+00:00
-- url     : https://prove2.me/submissions/81b466ac-e797-493e-9959-eddcd8d5a10e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensSt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensQ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW
open NumberField IsDedekindDomain Filter Asymptotics
open scoped nonZeroDivisors
namespace PI.VolStabW
theorem _root_.solution {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    qV v = (Ideal.absNorm v.asIdeal : ℝ) := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  rfl
end PI.VolStabW
