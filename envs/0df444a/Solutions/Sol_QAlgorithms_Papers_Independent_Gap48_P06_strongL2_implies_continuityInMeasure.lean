-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P06.strongL2_implies_continuityInMeasure
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T21:46:06.715962+00:00
-- url     : https://prove2.me/submissions/ee278df0-8d9e-4b0f-8ae3-88756772d9e2

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P06
noncomputable section

open MeasureTheory ProbabilityTheory Filter

open scoped Topology ENNReal NNReal

open QAlgorithms.Papers.Independent.Gap48.P06

theorem g73m_cheb {X K : Type*} [MeasurableSpace X] [RCLike K] (mu : Measure X)
    (f g : Lp K 2 mu) (eps : ℝ) (heps : 0 < eps) :
    mu {x | eps ≤ ‖(f : X → K) x - (g : X → K) x‖} ≤
      (ENNReal.ofReal eps)⁻¹ ^ (2 : ℝ≥0∞).toReal *
        (ENNReal.ofReal ‖f - g‖) ^ (2 : ℝ≥0∞).toReal := by
  have hset : {x | eps ≤ ‖(f : X → K) x - (g : X → K) x‖} =
      {x | ENNReal.ofReal eps ≤ ‖((f : X → K) - (g : X → K)) x‖ₑ} := by
    ext x
    simp only [Set.mem_ofPred_eq, Pi.sub_apply]
    rw [← ofReal_norm, ENNReal.ofReal_le_ofReal_iff (norm_nonneg _)]
  rw [hset]
  have h := meas_ge_le_mul_pow_eLpNorm_enorm mu (p := 2) (by norm_num) (by norm_num)
    ((Lp.aestronglyMeasurable f).sub (Lp.aestronglyMeasurable g))
    (ε := ENNReal.ofReal eps) (by simpa using heps) (by simp)
  have he : eLpNorm ((f : X → K) - (g : X → K)) 2 mu = ENNReal.ofReal ‖f - g‖ := by
    rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _)]
    exact eLpNorm_congr_ae (Lp.coeFn_sub f g).symm
  rwa [he] at h

theorem g73m_tendsto {S X K : Type*} [TopologicalSpace S] [MeasurableSpace X] [RCLike K]
    (mu : Measure X) (F : S → Lp K 2 mu) (s0 : S) (hF : ContinuousAt F s0) :
    ContinuousInMeasureAt mu (fun s x => (F s : X → K) x) s0 := by
  intro eps heps
  have h1 : Tendsto (fun s => ‖F s - F s0‖) (𝓝 s0) (𝓝 0) := by
    have := (hF.sub (continuousAt_const (y := F s0))).norm.tendsto
    simpa using this
  have h2 : Tendsto (fun s => (ENNReal.ofReal eps)⁻¹ ^ (2 : ℝ≥0∞).toReal *
        (ENNReal.ofReal ‖F s - F s0‖) ^ (2 : ℝ≥0∞).toReal) (𝓝 s0) (𝓝 0) := by
    have h3 : Tendsto (fun s => ENNReal.ofReal ‖F s - F s0‖) (𝓝 s0) (𝓝 0) := by
      simpa using (ENNReal.tendsto_ofReal h1)
    have h4 : Tendsto (fun s => (ENNReal.ofReal ‖F s - F s0‖) ^ (2 : ℝ≥0∞).toReal)
        (𝓝 s0) (𝓝 0) := by
      have := (ENNReal.continuous_rpow_const (y := (2 : ℝ≥0∞).toReal)).tendsto 0
      have h0 : (0 : ℝ≥0∞) ^ (2 : ℝ≥0∞).toReal = 0 := by
        rw [ENNReal.zero_rpow_of_pos (by norm_num)]
      rw [h0] at this
      exact this.comp h3
    have := ENNReal.Tendsto.const_mul h4
      (a := (ENNReal.ofReal eps)⁻¹ ^ (2 : ℝ≥0∞).toReal) (Or.inr (by
        apply ENNReal.rpow_ne_top_of_nonneg (by norm_num)
        simpa using heps))
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h2
    (fun _ => bot_le) (fun s => g73m_cheb mu (F s) (F s0) eps heps)

theorem solution
    {S X K : Type*} [Semigroup S] [TopologicalSpace S] [ContinuousMul S]
    [MeasurableSpace X] [RCLike K] (mu : Measure X)
    (P : CompatiblePositiveSemigroup S X K mu)
    (hstrong : ∀ f, Continuous (fun s => P.onL2 s f)) :
    ∀ (f : Lp K 2 mu) (s0 : S),
      ContinuousInMeasureAt mu (fun s x => (P.onL2 s f) x) s0 := by
  intro f s0
  exact g73m_tendsto mu (fun s => P.onL2 s f) s0 ((hstrong f).continuousAt)

end
