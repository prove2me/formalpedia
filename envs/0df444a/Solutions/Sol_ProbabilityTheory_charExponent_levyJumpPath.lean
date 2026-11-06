-- Prove2me | solution 1 for ProbabilityTheory.charExponent_levyJumpPath
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T19:54:29.079012+00:00
-- url     : https://prove2.me/submissions/05387a54-ed39-4930-8c3e-7194c0358868

import Definitions.Def_LeanLevy_RandomMeasure_LevyJumpLaw
import Definitions.Def_LeanLevy_Processes_Cadlag
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Probability.Martingale.OptionalStopping
import Definitions.Def_LeanLevy_RandomMeasure_LevyJumpPath
import Theorems.Thm_ProbabilityTheory_isLevyProcess_levyJumpPath
import Theorems.Thm_ProbabilityTheory_charFun_map_levyJumpPath

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Set Topology Complex
open scoped NNReal ENNReal BigOperators

variable {Ω : Type} [MeasurableSpace Ω] {K : ℕ → Ω → ℕ}
  {X : ℕ → ℕ → Ω → ℝ × ℝ} {ν : Measure ℝ} [SigmaFinite ν]
  {μ : Measure Ω}

/-- Principal-branch logarithm proof from the pinned LeanLevy source. -/
theorem solution [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X ((volume : Measure ℝ).prod ν) μ) (hν : IsLevyMeasure ν)
    (b : ℝ) (ξ : ℝ) :
    (isLevyProcess_levyJumpPath hd hν b).charExponent ξ
      = (LevyKhintchineTriple.mk b 0 ν hν).exponent ξ := by
  set ψ : ℂ := (LevyKhintchineTriple.mk b 0 ν hν).exponent ξ with hψ
  simp only [IsLevyProcess.charExponent]
  apply Filter.Tendsto.limUnder_eq
  apply tendsto_const_nhds.congr'
  have hcont : Filter.Tendsto (fun t : ℝ≥0 => (t : ℝ) * ψ.im) (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous (fun t : ℝ≥0 => (t : ℝ) * ψ.im) :=
      NNReal.continuous_coe.mul continuous_const
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin,
    hcont.eventually (Metric.ball_mem_nhds (0 : ℝ) Real.pi_pos)] with t (ht : 0 < t) htim
  have hne : ((t : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast NNReal.coe_ne_zero.mpr (ne_of_gt ht)
  have habs : |(t : ℝ) * ψ.im| < Real.pi := by simpa [Real.dist_eq] using htim
  obtain ⟨h1, h2⟩ := abs_lt.mp habs
  have him : (((t : ℝ) : ℂ) * ψ).im = (t : ℝ) * ψ.im := by simp [Complex.mul_im]
  have hlog : Complex.log (Complex.exp (((t : ℝ) : ℂ) * ψ)) = ((t : ℝ) : ℂ) * ψ :=
    Complex.log_exp (by rw [him]; exact h1) (by rw [him]; exact le_of_lt h2)
  rw [charFun_map_levyJumpPath hd hν b t ξ, hlog, eq_div_iff hne]
  ring
