-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P06.stationaryProcess_continuityInMeasure
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T21:49:23.247178+00:00
-- url     : https://prove2.me/submissions/a0fb1826-72c8-494f-8106-7faf955431d8

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
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (nu : Measure (G → ℝ)) [IsProbabilityMeasure nu]
    (hstationary : ∀ g, MeasurePreserving (pathShift g) nu nu)
    (hsquare : MemLp (fun w : G → ℝ => w 1) 2 nu)
    (hstrong : ∀ f, Continuous (fun g => pathKoopman nu hstationary g f)) :
    ∀ eps : ℝ, 0 < eps →
      Tendsto (fun g => nu {w | eps ≤ |w g - w 1|}) (𝓝 (1 : G)) (𝓝 0) := by
  intro eps heps
  have hsq : MemLp (fun w : G → ℝ => ((w 1 : ℝ) : ℂ)) 2 nu := by
    have := hsquare.ofReal (K := ℂ)
    simpa using this
  set f0 : Lp ℂ 2 nu := hsq.toLp _ with hf0
  have hK : ∀ g, (pathKoopman nu hstationary g f0 : (G → ℝ) → ℂ) =ᵐ[nu]
      fun w => ((w g : ℝ) : ℂ) := by
    intro g
    have h1 := Lp.coeFn_compMeasurePreserving f0 (hstationary g⁻¹)
    have h2 : (f0 : (G → ℝ) → ℂ) ∘ pathShift g⁻¹ =ᵐ[nu]
        (fun w : G → ℝ => ((w 1 : ℝ) : ℂ)) ∘ pathShift g⁻¹ := by
      apply ae_eq_comp (hstationary g⁻¹).measurable.aemeasurable
      rw [(hstationary g⁻¹).map_eq]
      exact hsq.coeFn_toLp
    have h3 := h1.trans h2
    refine h3.trans (Eventually.of_forall fun w => ?_)
    simp [pathShift]
  have key := g73m_tendsto nu (fun g => pathKoopman nu hstationary g f0) 1
    (hstrong f0).continuousAt eps heps
  refine key.congr fun g => ?_
  apply measure_congr
  filter_upwards [hK g, hK 1] with w hw1 hw2
  change (eps ≤ ‖(pathKoopman nu hstationary g f0 : (G → ℝ) → ℂ) w -
      (pathKoopman nu hstationary 1 f0 : (G → ℝ) → ℂ) w‖) = (eps ≤ |w g - w 1|)
  rw [hw1, hw2, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]

end
