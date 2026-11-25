-- Prove2me | solution 1 for PI.VolStabW.SdTestInfW.measurable_freq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:06:37.898649+00:00
-- url     : https://prove2.me/submissions/b84a5c45-8ac8-400e-aa90-fa7890cb627f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_SdUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DensInfAll
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_RealCharacter
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_SdTestInf
import Theorems.Thm_PI_VolStabW_SdTestInfW_arg_exp_small

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
    (hβ : ∀ y, ∀ s : ℝ, χ (s • v) y = exp (↑(β y * s) * I)) : Measurable β := by
  let g : ℕ → W → ℝ := fun m y => ((m : ℝ) + 1) * arg (χ ((1 / ((m : ℝ) + 1)) • v) y)
  have hg : ∀ m, Measurable (g m) := fun m =>
    measurable_const.mul (measurable_arg.comp (h.contR _).measurable)
  refine measurable_of_tendsto_metrizable hg (tendsto_pi_nhds.2 fun y => ?_)
  have ht : Tendsto (fun m : ℕ => β y * (1 / ((m : ℝ) + 1))) atTop (𝓝 (β y * 0)) :=
    (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul (β y)
  rw [mul_zero] at ht
  have hev := ht (Ioo_mem_nhds (neg_lt_zero.2 Real.pi_pos) Real.pi_pos)
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [hev] with m hm
  simp only [g]
  rw [hβ y, arg_exp_small hm]
  field_simp
end PI.VolStabW.SdTestInfW
