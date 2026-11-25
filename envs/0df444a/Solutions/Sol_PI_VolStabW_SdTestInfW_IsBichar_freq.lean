-- Prove2me | solution 1 for PI.VolStabW.SdTestInfW.IsBichar.freq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:13:24.626981+00:00
-- url     : https://prove2.me/submissions/7ca444c0-5ab7-4efe-aed3-e2e5b3984e70

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_SdUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DensInfAll
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_RealCharacter
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_SdTestInf
import Theorems.Thm_PI_VolStabW_SdTestInfW_char_real
import Theorems.Thm_UpperTheory_Reformulated_B_UnitaryCharacterOfReals_char_real


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
namespace IsBichar
theorem _root_.solution {χ : W → W → ℂ} (h : IsBichar χ) (v y : W) :
    ∃ β : ℝ, ∀ s : ℝ, χ (s • v) y = exp (↑(β * s) * I) :=
  char_real (fun s => χ (s • v) y) ((h.contL y).comp (continuous_id.smul continuous_const))
    (fun s t => by simp only [add_smul]; exact h.addL _ _ y) (fun s => h.norm1 _ y)
end IsBichar
end PI.VolStabW.SdTestInfW
