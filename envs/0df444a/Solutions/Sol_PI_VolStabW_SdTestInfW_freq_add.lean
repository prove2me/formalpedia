-- Prove2me | solution 1 for PI.VolStabW.SdTestInfW.freq_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:24:10.675807+00:00
-- url     : https://prove2.me/submissions/9d8428e2-366b-4da4-a9ed-fdc26822288b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_SdUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DensInfAll
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_RealCharacter
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_SdTestInf
import Theorems.Thm_PI_VolStabW_SdTestInfW_freq_unique

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
open PI.VolStabW.SdTestInfW
open MeasureTheory Complex Filter Topology
open scoped RealInnerProductSpace
variable {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W]
namespace PI.VolStabW.SdTestInfW
theorem _root_.solution {χ : W → W → ℂ} (h : IsBichar χ) (v : W) (β : W → ℝ)
    (hβ : ∀ y, ∀ s : ℝ, χ (s • v) y = exp (↑(β y * s) * I)) (y y' : W) :
    β (y + y') = β y + β y' := by
  refine freq_unique fun s => ?_
  rw [← hβ, h.addR, hβ, hβ, ← Complex.exp_add]
  congr 1; push_cast; ring
end PI.VolStabW.SdTestInfW
