-- Prove2me | solution 1 for PI.RhsWLim.W.testJ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:17:27.749646+00:00
-- url     : https://prove2.me/submissions/dc3e96d9-1ab6-4724-9645-884a3e9b06ad

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_HaarUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_ConstCut
import Theorems.Thm_PI_RhsWLim_W_annU_open

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Matrix
open scoped ENNReal
open PI PI.RhsWLim PI.RhsWLim.W
open PI.RhsWLim
namespace PI.RhsWLim.W
theorem _root_.solution (k : ℕ) (T T' : ℝ) (hTT : 0 < T * T') :
    0 < ∫⁻ ζ : ℂ, ENNReal.ofReal (zWeight k T T' ζ) * (annU T T').indicator 1 ζ ∧
      ∫⁻ ζ : ℂ, ENNReal.ofReal (zWeight k T T' ζ) * (annU T T').indicator 1 ζ < ⊤ := by
  have hAo : IsOpen (annU T T') := annU_open T T'
  constructor
  ·
    have hVo : IsOpen {ζ : ℂ | 2 * (T * T') < Complex.normSq ζ ∧ Complex.normSq ζ < 3 * (T * T')} :=
      (isOpen_lt continuous_const Complex.continuous_normSq).inter
        (isOpen_lt Complex.continuous_normSq continuous_const)
    have hVne : {ζ : ℂ | 2 * (T * T') < Complex.normSq ζ ∧ Complex.normSq ζ < 3 * (T * T')}.Nonempty := by
      refine ⟨((Real.sqrt (5 / 2 * (T * T')) : ℝ) : ℂ), ?_, ?_⟩ <;>
        rw [Complex.normSq_ofReal, Real.mul_self_sqrt (by positivity)] <;> linarith
    have hVpos := hVo.measure_pos volume hVne
    have hle : ∀ ζ, ENNReal.ofReal ((T * T') ^ (k - 1)) *
        {ζ : ℂ | 2 * (T * T') < Complex.normSq ζ ∧ Complex.normSq ζ < 3 * (T * T')}.indicator 1 ζ ≤
        ENNReal.ofReal (zWeight k T T' ζ) * (annU T T').indicator 1 ζ := by
      intro ζ
      by_cases hζ : 2 * (T * T') < Complex.normSq ζ ∧ Complex.normSq ζ < 3 * (T * T')
      · have hU : ζ ∈ annU T T' := ⟨by linarith [hζ.1], by linarith [hζ.2]⟩
        have hV : ζ ∈ {ζ : ℂ | 2 * (T * T') < Complex.normSq ζ ∧ Complex.normSq ζ < 3 * (T * T')} := hζ
        rw [Set.indicator_of_mem hV, Set.indicator_of_mem hU, Pi.one_apply, mul_one, mul_one]
        apply ENNReal.ofReal_le_ofReal
        unfold zWeight
        rw [if_pos (by linarith [hζ.1])]
        exact pow_le_pow_left₀ hTT.le (by linarith [hζ.1]) _
      · have hV : ζ ∉ {ζ : ℂ | 2 * (T * T') < Complex.normSq ζ ∧ Complex.normSq ζ < 3 * (T * T')} := hζ
        simp [Set.indicator_apply, hV]
    calc (0 : ℝ≥0∞) < ENNReal.ofReal ((T * T') ^ (k - 1)) *
          volume {ζ : ℂ | 2 * (T * T') < Complex.normSq ζ ∧ Complex.normSq ζ < 3 * (T * T')} :=
          ENNReal.mul_pos (ENNReal.ofReal_pos.2 (pow_pos hTT _)).ne' hVpos.ne'
      _ = ∫⁻ ζ, ENNReal.ofReal ((T * T') ^ (k - 1)) *
          {ζ : ℂ | 2 * (T * T') < Complex.normSq ζ ∧ Complex.normSq ζ < 3 * (T * T')}.indicator 1 ζ := by
          rw [lintegral_const_mul _ (measurable_one.indicator hVo.measurableSet),
            lintegral_indicator_one hVo.measurableSet]
      _ ≤ _ := lintegral_mono hle
  · have hM : ∀ ζ, ENNReal.ofReal (zWeight k T T' ζ) * (annU T T').indicator 1 ζ ≤
        ENNReal.ofReal ((3 * (T * T')) ^ (k - 1)) * (annU T T').indicator 1 ζ := by
      intro ζ
      by_cases hζ : ζ ∈ annU T T'
      · rw [Set.indicator_of_mem hζ, Pi.one_apply, mul_one, mul_one]
        apply ENNReal.ofReal_le_ofReal
        unfold zWeight
        rw [if_pos hζ.1.le]
        exact pow_le_pow_left₀ (by linarith [hζ.1]) (by linarith [hζ.2]) _
      · simp [Set.indicator_apply, hζ]
    have hsub : annU T T' ⊆ Metric.ball 0 (2 * Real.sqrt (T * T') + 1) := by
      intro ζ hζ
      rw [Metric.mem_ball, dist_zero_right]
      have h1 : ‖ζ‖ ^ 2 < (2 * Real.sqrt (T * T')) ^ 2 := by
        rw [← Complex.normSq_eq_norm_sq, mul_pow, Real.sq_sqrt hTT.le]
        linarith [hζ.2]
      have h2 := lt_of_pow_lt_pow_left₀ 2 (by positivity) h1
      linarith
    have hfin : volume (annU T T') < ⊤ := (measure_mono hsub).trans_lt measure_ball_lt_top
    calc _ ≤ ∫⁻ ζ, ENNReal.ofReal ((3 * (T * T')) ^ (k - 1)) * (annU T T').indicator 1 ζ :=
          lintegral_mono hM
      _ = ENNReal.ofReal ((3 * (T * T')) ^ (k - 1)) * volume (annU T T') := by
          rw [lintegral_const_mul _ (measurable_one.indicator hAo.measurableSet),
            lintegral_indicator_one hAo.measurableSet]
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin
end PI.RhsWLim.W
