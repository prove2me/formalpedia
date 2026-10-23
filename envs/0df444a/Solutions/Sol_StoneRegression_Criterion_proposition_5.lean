-- Prove2me | solution 1 for StoneRegression.Criterion.proposition_5
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T06:18:37.919107+00:00
-- url     : https://prove2.me/submissions/65ed9b06-63bb-49ed-a86a-776a4c5df20c

import Mathlib
import Definitions.Def_StoneRegression_Criterion_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BoundedContinuousFunction


namespace StoneRegression.Criterion

lemma p1_meas_wAt {d : ℕ} (W : WeightSeq d) (hW : MeasurableWeights W) (n : ℕ) (i : Fin n) :
    Measurable (fun ω : ℕ → EuclideanSpace ℝ (Fin d) => wAt W n ω i) := by
  have h1 : Measurable (fun ω : ℕ → EuclideanSpace ℝ (Fin d) => (ω 0, sample ω n)) :=
    (measurable_pi_apply 0).prodMk (measurable_pi_lambda _ (fun j => measurable_pi_apply _))
  exact (measurable_pi_apply i).comp ((hW n).comp h1)

lemma p1_marg {d : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ] (j : ℕ)
    (g : EuclideanSpace ℝ (Fin d) → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ ω, g (ω j) ∂(xLaw μ) = ∫⁻ x, g x ∂μ :=
  (measurePreserving_eval_infinitePi (fun _ : ℕ => μ) j).lintegral_comp hg

lemma p1_squeeze (S : ℕ → ℝ≥0∞) (A : ℝ≥0∞) (hA : A ≠ ∞)
    (h : ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 → ∀ᶠ n in atTop, S n ≤ A * ENNReal.ofReal ρ) :
    Tendsto S atTop (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have ht : Tendsto (fun k : ℕ => A * ENNReal.ofReal (1 / ((k:ℝ) + 1))) atTop (𝓝 0) := by
    have := ENNReal.Tendsto.const_mul
      (ENNReal.tendsto_ofReal tendsto_one_div_add_atTop_nhds_zero_nat) (Or.inr hA)
    simpa using this
  obtain ⟨k, hk⟩ := (ht.eventually (gt_mem_nhds hε)).exists
  have hk1 : 1 / ((k:ℝ) + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]; linarith [(k.cast_nonneg : (0:ℝ) ≤ k)]
  filter_upwards [h (1 / ((k:ℝ) + 1)) (by positivity) hk1] with n hn
  exact hn.trans hk.le

lemma p1_l1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (g : ℕ → Ω → ℝ) (hg : ∀ n, Measurable (g n)) (D : ℝ)
    (hb : ∀ᶠ n in atTop, ∀ᵐ ω ∂P, 0 ≤ g n ω ∧ g n ω ≤ D)
    (hconv : TendstoInMeasure P g atTop (fun _ => 0)) :
    Tendsto (fun n => ∫⁻ ω, ENNReal.ofReal (g n ω) ∂P) atTop (𝓝 0) := by
  refine p1_squeeze _ (1 + ENNReal.ofReal D) (by finiteness) ?_
  intro ρ hρ hρ1
  have hc := (tendstoInMeasure_iff_dist.1 hconv) ρ hρ
  have hev := ENNReal.tendsto_nhds_zero.1 hc (ENNReal.ofReal ρ) (ENNReal.ofReal_pos.2 hρ)
  filter_upwards [hev, hb] with n hn hbn
  have hms : MeasurableSet {ω | ρ ≤ dist (g n ω) 0} :=
    measurableSet_le measurable_const ((hg n).dist measurable_const)
  calc ∫⁻ ω, ENNReal.ofReal (g n ω) ∂P
      ≤ ∫⁻ ω, (ENNReal.ofReal ρ + ENNReal.ofReal D * {ω | ρ ≤ dist (g n ω) 0}.indicator 1 ω) ∂P := by
        refine lintegral_mono_ae ?_
        filter_upwards [hbn] with ω hω
        by_cases hc : ρ ≤ dist (g n ω) 0
        · rw [Set.indicator_of_mem (show ω ∈ {ω | ρ ≤ dist (g n ω) 0} from hc)]
          simp only [Pi.one_apply, mul_one]
          exact le_add_left (ENNReal.ofReal_le_ofReal hω.2)
        · rw [Set.indicator_of_notMem (show ω ∉ {ω | ρ ≤ dist (g n ω) 0} from hc)]
          simp only [mul_zero, add_zero]
          rw [Real.dist_eq, sub_zero, abs_of_nonneg hω.1] at hc
          exact ENNReal.ofReal_le_ofReal (not_le.1 hc).le
    _ = ENNReal.ofReal ρ + ENNReal.ofReal D * P {ω | ρ ≤ dist (g n ω) 0} := by
        rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
          lintegral_const_mul _ (measurable_one.indicator hms), lintegral_indicator_one hms]
    _ ≤ ENNReal.ofReal ρ + ENNReal.ofReal D * ENNReal.ofReal ρ := by gcongr
    _ = (1 + ENNReal.ofReal D) * ENNReal.ofReal ρ := by ring

lemma p1_tri (r : ℝ) (hr : 1 ≤ r) (p q s : ℝ≥0∞) :
    (p + q + s) ^ r ≤ ((2:ℝ≥0∞) ^ (r - 1) * 2 ^ (r - 1)) * (p ^ r + q ^ r + s ^ r) := by
  have h1 := ENNReal.rpow_add_le_mul_rpow_add_rpow (p + q) s hr
  have h2 := ENNReal.rpow_add_le_mul_rpow_add_rpow p q hr
  have h3 : (1:ℝ≥0∞) ≤ 2 ^ (r - 1) := by
    have := ENNReal.rpow_le_rpow_of_exponent_le (x := (2:ℝ≥0∞)) (by norm_num)
      (show (0:ℝ) ≤ r - 1 by linarith)
    simpa using this
  calc (p + q + s) ^ r ≤ 2 ^ (r - 1) * ((p + q) ^ r + s ^ r) := h1
    _ ≤ 2 ^ (r - 1) * (2 ^ (r - 1) * (p ^ r + q ^ r) + 2 ^ (r - 1) * s ^ r) := by
        gcongr
        exact le_mul_of_one_le_left' h3
    _ = _ := by ring

instance p1_xLaw_prob {d : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (xLaw μ) := by
  unfold xLaw; infer_instance

noncomputable def p1Z {d : ℕ} (W : WeightSeq d) (a : ℝ) (n : ℕ) (ω : ℕ → EuclideanSpace ℝ (Fin d)) : ℝ :=
  ∑ i : Fin n, |wAt W n ω i| * (if a < ‖ω (i.val + 1) - ω 0‖ then 1 else 0)

theorem p1_core {d : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ]
    (W : WeightSeq d) (hW : MeasurableWeights W)
    (h1 : ∃ C : ℝ≥0, 1 ≤ C ∧ Cond1 μ W C) (h2 : ∃ D : ℝ, 1 ≤ D ∧ Cond2 μ W D) (h3 : Cond3 μ W)
    (r : ℝ) (hr : 1 ≤ r) (f : EuclideanSpace ℝ (Fin d) → ℝ) (hf : Measurable f)
    (hfr : ∫⁻ x, ‖f x‖ₑ ^ r ∂μ < ∞) :
    Tendsto (fun n => ∫⁻ ω, ∑ i : Fin n,
        ‖wAt W n ω i‖ₑ * ‖f (ω (i.val + 1)) - f (ω 0)‖ₑ ^ r ∂(xLaw μ)) atTop (𝓝 0) := by
  obtain ⟨C, hC1, hC⟩ := h1
  obtain ⟨D, hD1, hD⟩ := h2
  have hr0 : 0 ≤ r := by linarith
  set K : ℝ≥0∞ := (2:ℝ≥0∞) ^ (r - 1) * 2 ^ (r - 1) with hK
  have hKtop : K ≠ ∞ := by
    have : (2:ℝ≥0∞) ^ (r - 1) ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg (by linarith) (by norm_num)
    exact ENNReal.mul_ne_top this this
  have hmw : ∀ n (i : Fin n), Measurable (fun ω => wAt W n ω i) := p1_meas_wAt W hW
  refine p1_squeeze _ (K * ((C:ℝ≥0∞) + ENNReal.ofReal D + 1 + ENNReal.ofReal D))
    (ENNReal.mul_ne_top hKtop (by finiteness)) ?_
  intro ρ hρ hρ1
  have hp0 : ENNReal.ofReal r ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero]; linarith
  have hptop : ENNReal.ofReal r ≠ ∞ := ENNReal.ofReal_ne_top
  have hrt : (ENNReal.ofReal r).toReal = r := ENNReal.toReal_ofReal hr0
  have hfL : MemLp f (ENNReal.ofReal r) μ := by
    refine ⟨hf.aestronglyMeasurable, ?_⟩
    rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hp0 hptop, hrt]
    exact hfr
  obtain ⟨φ, hφc, hφn, hφcont, -⟩ :=
    hfL.exists_hasCompactSupport_eLpNorm_sub_le hptop (ENNReal.ofReal_pos.2 hρ).ne'
  have hφm : Measurable φ := hφcont.measurable
  have hint : ∫⁻ x, ‖f x - φ x‖ₑ ^ r ∂μ ≤ ENNReal.ofReal ρ := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hptop, hrt] at hφn
    have := ENNReal.rpow_le_rpow hφn hr0
    rw [← ENNReal.rpow_mul, one_div_mul_cancel (by linarith), ENNReal.rpow_one] at this
    simp only [Pi.sub_apply] at this
    exact this.trans (ENNReal.rpow_le_self_of_le_one (ENNReal.ofReal_le_one.2 hρ1) hr)
  obtain ⟨M, hM⟩ := hφc.exists_bound_of_continuous hφcont
  obtain ⟨δ, hδ, hδφ⟩ :=
    Metric.uniformContinuous_iff.1 (hφc.uniformContinuous_of_continuous hφcont) ρ hρ
  set a : ℝ := δ / 2 with ha
  have ha0 : 0 < a := by positivity
  set B : ℝ≥0∞ := ENNReal.ofReal (2 * M) ^ r with hB
  have hBtop : B ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg hr0 ENNReal.ofReal_ne_top
  have hφpt : ∀ x y : EuclideanSpace ℝ (Fin d), ‖φ y - φ x‖ₑ ^ r ≤
      ENNReal.ofReal ρ + B * ENNReal.ofReal (if a < ‖y - x‖ then 1 else 0) := by
    intro x y
    split_ifs with hxy
    · rw [ENNReal.ofReal_one, mul_one]
      refine le_add_left ?_
      refine ENNReal.rpow_le_rpow ?_ hr0
      rw [← ofReal_norm]
      apply ENNReal.ofReal_le_ofReal
      calc ‖φ y - φ x‖ ≤ ‖φ y‖ + ‖φ x‖ := norm_sub_le _ _
        _ ≤ 2 * M := by linarith [hM x, hM y]
    · rw [ENNReal.ofReal_zero, mul_zero, add_zero]
      have hd : dist y x < δ := by rw [dist_eq_norm]; linarith [not_lt.1 hxy]
      have h5 := hδφ hd
      rw [dist_eq_norm] at h5
      calc ‖φ y - φ x‖ₑ ^ r ≤ ENNReal.ofReal ρ ^ r := by
            gcongr
            rw [← ofReal_norm]; exact ENNReal.ofReal_le_ofReal h5.le
        _ ≤ ENNReal.ofReal ρ := ENNReal.rpow_le_self_of_le_one (ENNReal.ofReal_le_one.2 hρ1) hr
  let Z : ℕ → (ℕ → EuclideanSpace ℝ (Fin d)) → ℝ := p1Z W a
  have hZm : ∀ n, Measurable (Z n) := by
    intro n
    simp only [Z, p1Z]
    refine Finset.measurable_sum _ (fun i _ => ((hmw n i).abs).mul ?_)
    have hnm : Measurable (fun ω : ℕ → EuclideanSpace ℝ (Fin d) => ‖ω (i.val + 1) - ω 0‖) :=
      ((measurable_pi_apply (i.val + 1)).sub (measurable_pi_apply 0)).norm
    have hs : MeasurableSet {ω : ℕ → EuclideanSpace ℝ (Fin d) | a < ‖ω (i.val + 1) - ω 0‖} :=
      measurableSet_lt measurable_const hnm
    exact Measurable.ite hs measurable_const measurable_const
  have hZb : ∀ᶠ n in atTop, ∀ᵐ ω ∂(xLaw μ), 0 ≤ Z n ω ∧ Z n ω ≤ D := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    filter_upwards [hD n hn] with ω hω
    simp only [Z, p1Z]
    constructor
    · exact Finset.sum_nonneg (fun i _ => mul_nonneg (abs_nonneg _) (by split_ifs <;> norm_num))
    · refine le_trans (Finset.sum_le_sum (fun i _ => ?_)) hω
      have : (if a < ‖ω (i.val + 1) - ω 0‖ then (1:ℝ) else 0) ≤ 1 := by split_ifs <;> norm_num
      calc |wAt W n ω i| * (if a < ‖ω (i.val + 1) - ω 0‖ then (1:ℝ) else 0)
          ≤ |wAt W n ω i| * 1 := mul_le_mul_of_nonneg_left this (abs_nonneg _)
        _ = |wAt W n ω i| := mul_one _
  have hZl := p1_l1 (xLaw μ) Z hZm D hZb (h3 a ha0)
  have hZl' : Tendsto (fun n => B * ∫⁻ ω, ENNReal.ofReal (Z n ω) ∂(xLaw μ)) atTop (𝓝 0) := by
    have := ENNReal.Tendsto.const_mul hZl (Or.inr hBtop)
    simpa using this
  have hev := ENNReal.tendsto_nhds_zero.1 hZl' (ENNReal.ofReal ρ) (ENNReal.ofReal_pos.2 hρ)
  filter_upwards [hev, eventually_ge_atTop 1] with n hn hn1
  have hS : ∀ ω : ℕ → EuclideanSpace ℝ (Fin d), ∑ i : Fin n, ‖wAt W n ω i‖ₑ =
      ENNReal.ofReal (∑ i : Fin n, |wAt W n ω i|) := by
    intro ω
    rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => abs_nonneg _)]
    simp [Real.enorm_eq_ofReal_abs]
  have hpt : ∀ ω : ℕ → EuclideanSpace ℝ (Fin d),
      ∑ i : Fin n, ‖wAt W n ω i‖ₑ * ‖f (ω (i.val + 1)) - f (ω 0)‖ₑ ^ r ≤
      K * ((∑ i : Fin n, ‖wAt W n ω i‖ₑ * ‖f (ω (i.val + 1)) - φ (ω (i.val + 1))‖ₑ ^ r)
        + ENNReal.ofReal ρ * (∑ i : Fin n, ‖wAt W n ω i‖ₑ)
        + B * ENNReal.ofReal (Z n ω)
        + (∑ i : Fin n, ‖wAt W n ω i‖ₑ) * ‖f (ω 0) - φ (ω 0)‖ₑ ^ r) := by
    intro ω
    have hZe : ENNReal.ofReal (Z n ω) = ∑ i : Fin n, ‖wAt W n ω i‖ₑ *
        ENNReal.ofReal (if a < ‖ω (i.val + 1) - ω 0‖ then 1 else 0) := by
      simp only [Z, p1Z]
      rw [ENNReal.ofReal_sum_of_nonneg
        (fun i _ => mul_nonneg (abs_nonneg _) (by split_ifs <;> norm_num))]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [ENNReal.ofReal_mul (abs_nonneg _), Real.enorm_eq_ofReal_abs]
    rw [hZe]
    calc ∑ i : Fin n, ‖wAt W n ω i‖ₑ * ‖f (ω (i.val + 1)) - f (ω 0)‖ₑ ^ r
        ≤ ∑ i : Fin n, ‖wAt W n ω i‖ₑ * (K * (‖f (ω (i.val + 1)) - φ (ω (i.val + 1))‖ₑ ^ r
            + (ENNReal.ofReal ρ + B * ENNReal.ofReal (if a < ‖ω (i.val + 1) - ω 0‖ then 1 else 0))
            + ‖f (ω 0) - φ (ω 0)‖ₑ ^ r)) := by
          refine Finset.sum_le_sum (fun i _ => ?_)
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          calc ‖f (ω (i.val + 1)) - f (ω 0)‖ₑ ^ r
              ≤ (‖f (ω (i.val + 1)) - φ (ω (i.val + 1))‖ₑ + ‖φ (ω (i.val + 1)) - φ (ω 0)‖ₑ
                  + ‖f (ω 0) - φ (ω 0)‖ₑ) ^ r := by
                refine ENNReal.rpow_le_rpow ?_ hr0
                have e : f (ω (i.val + 1)) - f (ω 0) = (f (ω (i.val + 1)) - φ (ω (i.val + 1)))
                    + (φ (ω (i.val + 1)) - φ (ω 0)) - (f (ω 0) - φ (ω 0)) := by ring
                rw [e]
                exact enorm_sub_le.trans (add_le_add (enorm_add_le _ _) le_rfl)
            _ ≤ K * (‖f (ω (i.val + 1)) - φ (ω (i.val + 1))‖ₑ ^ r
                  + ‖φ (ω (i.val + 1)) - φ (ω 0)‖ₑ ^ r + ‖f (ω 0) - φ (ω 0)‖ₑ ^ r) :=
                p1_tri r hr _ _ _
            _ ≤ _ := by
                refine mul_le_mul_of_nonneg_left ?_ (by positivity)
                exact add_le_add (add_le_add le_rfl (hφpt _ _)) le_rfl
      _ = _ := by
          have e : ∀ i : Fin n, ‖wAt W n ω i‖ₑ * (K * (‖f (ω (i.val + 1)) - φ (ω (i.val + 1))‖ₑ ^ r
            + (ENNReal.ofReal ρ + B * ENNReal.ofReal (if a < ‖ω (i.val + 1) - ω 0‖ then 1 else 0))
            + ‖f (ω 0) - φ (ω 0)‖ₑ ^ r)) = K * (‖wAt W n ω i‖ₑ *
              ‖f (ω (i.val + 1)) - φ (ω (i.val + 1))‖ₑ ^ r + ENNReal.ofReal ρ * ‖wAt W n ω i‖ₑ
              + B * (‖wAt W n ω i‖ₑ *
                ENNReal.ofReal (if a < ‖ω (i.val + 1) - ω 0‖ then 1 else 0))
              + ‖wAt W n ω i‖ₑ * ‖f (ω 0) - φ (ω 0)‖ₑ ^ r) := fun i => by ring
          rw [Finset.sum_congr rfl (fun i _ => e i), ← Finset.mul_sum, Finset.sum_add_distrib,
            Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
            ← Finset.sum_mul]
  have hm1 : Measurable (fun ω : ℕ → EuclideanSpace ℝ (Fin d) =>
      ∑ i : Fin n, ‖wAt W n ω i‖ₑ * ‖f (ω (i.val + 1)) - φ (ω (i.val + 1))‖ₑ ^ r) := by
    refine Finset.measurable_sum _ (fun i _ => ((hmw n i).enorm).mul ?_)
    exact (((hf.comp (measurable_pi_apply (i.val + 1))).sub
      (hφm.comp (measurable_pi_apply (i.val + 1)))).enorm).pow_const r
  have hm2 : Measurable (fun ω : ℕ → EuclideanSpace ℝ (Fin d) => ∑ i : Fin n, ‖wAt W n ω i‖ₑ) :=
    Finset.measurable_sum _ (fun i _ => (hmw n i).enorm)
  have hm3 : Measurable (fun ω : ℕ → EuclideanSpace ℝ (Fin d) => ENNReal.ofReal (Z n ω)) :=
    ENNReal.measurable_ofReal.comp (hZm n)
  have hs0 : Measurable (fun x : EuclideanSpace ℝ (Fin d) => ‖f x - φ x‖ₑ ^ r) :=
    ((hf.sub hφm).enorm).pow_const r
  have hmB : Measurable (fun ω : ℕ → EuclideanSpace ℝ (Fin d) =>
      (∑ i : Fin n, ‖wAt W n ω i‖ₑ * ‖f (ω (i.val + 1)) - φ (ω (i.val + 1))‖ₑ ^ r)
        + ENNReal.ofReal ρ * (∑ i : Fin n, ‖wAt W n ω i‖ₑ)) := hm1.add (hm2.const_mul _)
  have hmA : Measurable (fun ω : ℕ → EuclideanSpace ℝ (Fin d) =>
      (∑ i : Fin n, ‖wAt W n ω i‖ₑ * ‖f (ω (i.val + 1)) - φ (ω (i.val + 1))‖ₑ ^ r)
        + ENNReal.ofReal ρ * (∑ i : Fin n, ‖wAt W n ω i‖ₑ)
        + B * ENNReal.ofReal (Z n ω)) := hmB.add (hm3.const_mul _)
  -- the four bounds
  have hb1 : ∫⁻ ω, ∑ i : Fin n, ‖wAt W n ω i‖ₑ * ‖f (ω (i.val + 1)) - φ (ω (i.val + 1))‖ₑ ^ r
      ∂(xLaw μ) ≤ (C : ℝ≥0∞) * ENNReal.ofReal ρ := by
    have hcoe : ∀ z : ℝ, ((‖z‖₊ ^ r : ℝ≥0) : ℝ≥0∞) = ‖z‖ₑ ^ r := fun z => by
      rw [ENNReal.coe_rpow_of_nonneg _ hr0]; rfl
    have hfm' : Measurable (fun x : EuclideanSpace ℝ (Fin d) => ‖f x - φ x‖₊ ^ r) :=
      ((hf.sub hφm).nnnorm).pow_const r
    have := hC _ hfm' n hn1
    simp only [hcoe] at this
    exact this.trans (mul_le_mul_of_nonneg_left hint (by positivity))
  have hb2 : ∫⁻ ω, ∑ i : Fin n, ‖wAt W n ω i‖ₑ ∂(xLaw μ) ≤ ENNReal.ofReal D := by
    calc ∫⁻ ω, ∑ i : Fin n, ‖wAt W n ω i‖ₑ ∂(xLaw μ) ≤ ∫⁻ ω, ENNReal.ofReal D ∂(xLaw μ) := by
          refine lintegral_mono_ae ?_
          filter_upwards [hD n hn1] with ω hω
          rw [hS]; exact ENNReal.ofReal_le_ofReal hω
      _ = ENNReal.ofReal D := by rw [lintegral_const, measure_univ, mul_one]
  have hb4 : ∫⁻ ω, (∑ i : Fin n, ‖wAt W n ω i‖ₑ) * ‖f (ω 0) - φ (ω 0)‖ₑ ^ r ∂(xLaw μ) ≤
      ENNReal.ofReal D * ENNReal.ofReal ρ := by
    calc ∫⁻ ω, (∑ i : Fin n, ‖wAt W n ω i‖ₑ) * ‖f (ω 0) - φ (ω 0)‖ₑ ^ r ∂(xLaw μ)
        ≤ ∫⁻ ω, ENNReal.ofReal D * ‖f (ω 0) - φ (ω 0)‖ₑ ^ r ∂(xLaw μ) := by
          refine lintegral_mono_ae ?_
          filter_upwards [hD n hn1] with ω hω
          rw [hS]
          exact mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hω) (by positivity)
      _ = ENNReal.ofReal D * ∫⁻ x, ‖f x - φ x‖ₑ ^ r ∂μ := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            p1_marg μ 0 (fun x => ‖f x - φ x‖ₑ ^ r) hs0]
      _ ≤ ENNReal.ofReal D * ENNReal.ofReal ρ := mul_le_mul_of_nonneg_left hint (by positivity)
  calc ∫⁻ ω, ∑ i : Fin n, ‖wAt W n ω i‖ₑ * ‖f (ω (i.val + 1)) - f (ω 0)‖ₑ ^ r ∂(xLaw μ)
      ≤ ∫⁻ ω, K * ((∑ i : Fin n, ‖wAt W n ω i‖ₑ * ‖f (ω (i.val + 1)) - φ (ω (i.val + 1))‖ₑ ^ r)
        + ENNReal.ofReal ρ * (∑ i : Fin n, ‖wAt W n ω i‖ₑ)
        + B * ENNReal.ofReal (Z n ω)
        + (∑ i : Fin n, ‖wAt W n ω i‖ₑ) * ‖f (ω 0) - φ (ω 0)‖ₑ ^ r) ∂(xLaw μ) :=
        lintegral_mono hpt
    _ = K * ((∫⁻ ω, ∑ i : Fin n, ‖wAt W n ω i‖ₑ * ‖f (ω (i.val + 1)) - φ (ω (i.val + 1))‖ₑ ^ r
          ∂(xLaw μ))
        + ENNReal.ofReal ρ * (∫⁻ ω, ∑ i : Fin n, ‖wAt W n ω i‖ₑ ∂(xLaw μ))
        + B * (∫⁻ ω, ENNReal.ofReal (Z n ω) ∂(xLaw μ))
        + ∫⁻ ω, (∑ i : Fin n, ‖wAt W n ω i‖ₑ) * ‖f (ω 0) - φ (ω 0)‖ₑ ^ r ∂(xLaw μ)) := by
        rw [lintegral_const_mul' _ _ hKtop, lintegral_add_left hmA, lintegral_add_left hmB,
          lintegral_add_left hm1, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_const_mul' _ _ hBtop]
    _ ≤ K * ((C : ℝ≥0∞) * ENNReal.ofReal ρ + ENNReal.ofReal ρ * ENNReal.ofReal D
        + ENNReal.ofReal ρ + ENNReal.ofReal D * ENNReal.ofReal ρ) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact add_le_add (add_le_add (add_le_add hb1
          (mul_le_mul_of_nonneg_left hb2 (by positivity))) hn) hb4
    _ = K * ((C:ℝ≥0∞) + ENNReal.ofReal D + 1 + ENNReal.ofReal D) * ENNReal.ofReal ρ := by ring

lemma p5_jensen (r : ℝ) (hr : 1 ≤ r) {n : ℕ} (w e : Fin n → ℝ≥0∞) :
    (∑ i, w i * e i) ^ r ≤ (∑ i, w i) ^ (r - 1) * ∑ i, w i * e i ^ r := by
  have hr0 : 0 ≤ r := by linarith
  have h := ENNReal.inner_le_weight_mul_Lp_of_nonneg Finset.univ hr w e
  calc (∑ i, w i * e i) ^ r
      ≤ ((∑ i, w i) ^ (1 - r⁻¹) * (∑ i, w i * e i ^ r) ^ r⁻¹) ^ r := ENNReal.rpow_le_rpow h hr0
    _ = (∑ i, w i) ^ ((1 - r⁻¹) * r) * (∑ i, w i * e i ^ r) ^ (r⁻¹ * r) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hr0, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
    _ = _ := by
        have hne : r ≠ 0 := by linarith
        rw [show (1 - r⁻¹) * r = r - 1 by field_simp, inv_mul_cancel₀ hne, ENNReal.rpow_one]

theorem p5_core {d : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ]
    (W : WeightSeq d) (hW : MeasurableWeights W)
    (h1 : ∃ C : ℝ≥0, 1 ≤ C ∧ Cond1 μ W C) (h2 : ∃ D : ℝ, 1 ≤ D ∧ Cond2 μ W D) (h3 : Cond3 μ W)
    (h4 : Cond4 μ W)
    (r : ℝ) (hr : 1 ≤ r) (f : EuclideanSpace ℝ (Fin d) → ℝ) (hf : Measurable f)
    (hfr : ∫⁻ x, ‖f x‖ₑ ^ r ∂μ < ∞) :
    Tendsto (fun n => ∫⁻ ω,
        ‖∑ i : Fin n, wAt W n ω i * f (ω (i.val + 1)) - f (ω 0)‖ₑ ^ r ∂(xLaw μ)) atTop (𝓝 0) := by
  have hS1 := p1_core μ W hW h1 h2 h3 r hr f hf hfr
  obtain ⟨D, hD1, hD⟩ := h2
  have hr0 : 0 ≤ r := by linarith
  have hmw : ∀ n (i : Fin n), Measurable (fun ω => wAt W n ω i) := p1_meas_wAt W hW
  have hhm : Measurable (fun ω : ℕ → EuclideanSpace ℝ (Fin d) => ‖f (ω 0)‖ₑ ^ r) :=
    ((hf.comp (measurable_pi_apply 0)).enorm).pow_const r
  have hhi : ∫⁻ ω, ‖f (ω 0)‖ₑ ^ r ∂(xLaw μ) = ∫⁻ x, ‖f x‖ₑ ^ r ∂μ :=
    p1_marg μ 0 (fun x => ‖f x‖ₑ ^ r) (hf.enorm.pow_const r)
  have hDtop : ENNReal.ofReal (D + 1) ^ r ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg hr0 ENNReal.ofReal_ne_top
  have hS2 : Tendsto (fun n => ∫⁻ ω, ‖∑ i : Fin n, wAt W n ω i - 1‖ₑ ^ r * ‖f (ω 0)‖ₑ ^ r
      ∂(xLaw μ)) atTop (𝓝 0) := by
    refine p1_squeeze _ (∫⁻ x, ‖f x‖ₑ ^ r ∂μ + 1) (by finiteness) ?_
    intro ρ hρ hρ1
    have hAm : ∀ n, MeasurableSet {ω : ℕ → EuclideanSpace ℝ (Fin d) |
        ρ ≤ dist (∑ i : Fin n, wAt W n ω i) 1} := fun n =>
      measurableSet_le measurable_const
        ((Finset.measurable_sum _ (fun i _ => hmw n i)).dist measurable_const)
    have hPA : Tendsto (fun n => xLaw μ {ω : ℕ → EuclideanSpace ℝ (Fin d) |
        ρ ≤ dist (∑ i : Fin n, wAt W n ω i) 1}) atTop (𝓝 0) :=
      (tendstoInMeasure_iff_dist.1 h4) ρ hρ
    have hset := tendsto_setLIntegral_zero (μ := xLaw μ)
      (f := fun ω => ‖f (ω 0)‖ₑ ^ r) (by rw [hhi]; exact hfr.ne) hPA
    have hset' : Tendsto (fun n => ENNReal.ofReal (D + 1) ^ r * ∫⁻ ω in {ω : ℕ → EuclideanSpace ℝ (Fin d) |
        ρ ≤ dist (∑ i : Fin n, wAt W n ω i) 1}, ‖f (ω 0)‖ₑ ^ r ∂(xLaw μ)) atTop (𝓝 0) := by
      simpa using ENNReal.Tendsto.const_mul hset (Or.inr hDtop)
    filter_upwards [ENNReal.tendsto_nhds_zero.1 hset' (ENNReal.ofReal ρ)
      (ENNReal.ofReal_pos.2 hρ), eventually_ge_atTop 1] with n hn hn1
    calc ∫⁻ ω, ‖∑ i : Fin n, wAt W n ω i - 1‖ₑ ^ r * ‖f (ω 0)‖ₑ ^ r ∂(xLaw μ)
        ≤ ∫⁻ ω, (ENNReal.ofReal ρ * ‖f (ω 0)‖ₑ ^ r + ENNReal.ofReal (D + 1) ^ r *
            {ω : ℕ → EuclideanSpace ℝ (Fin d) | ρ ≤ dist (∑ i : Fin n, wAt W n ω i) 1}.indicator
              (fun ω => ‖f (ω 0)‖ₑ ^ r) ω) ∂(xLaw μ) := by
          refine lintegral_mono_ae ?_
          filter_upwards [hD n hn1] with ω hω
          by_cases hc : ω ∈ {ω : ℕ → EuclideanSpace ℝ (Fin d) |
              ρ ≤ dist (∑ i : Fin n, wAt W n ω i) 1}
          · rw [Set.indicator_of_mem hc]
            refine le_add_left ?_
            refine mul_le_mul_of_nonneg_right (ENNReal.rpow_le_rpow ?_ hr0) (by positivity)
            rw [Real.enorm_eq_ofReal_abs]
            apply ENNReal.ofReal_le_ofReal
            have habs : |∑ i : Fin n, wAt W n ω i| ≤ ∑ i : Fin n, |wAt W n ω i| :=
              Finset.abs_sum_le_sum_abs _ _
            calc |∑ i : Fin n, wAt W n ω i - 1| ≤ |∑ i : Fin n, wAt W n ω i| + |1| := abs_sub _ _
              _ ≤ D + 1 := by rw [abs_one]; linarith
          · rw [Set.indicator_of_notMem hc, mul_zero, add_zero]
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            have hlt : |∑ i : Fin n, wAt W n ω i - 1| < ρ := by
              simp only [Set.mem_setOf_eq, not_le, Real.dist_eq] at hc
              exact hc
            have hG : ‖∑ i : Fin n, wAt W n ω i - 1‖ₑ ≤ ENNReal.ofReal ρ := by
              rw [Real.enorm_eq_ofReal_abs]; exact ENNReal.ofReal_le_ofReal hlt.le
            exact (ENNReal.rpow_le_self_of_le_one (hG.trans (ENNReal.ofReal_le_one.2 hρ1)) hr).trans hG
      _ = ENNReal.ofReal ρ * ∫⁻ ω, ‖f (ω 0)‖ₑ ^ r ∂(xLaw μ) + ENNReal.ofReal (D + 1) ^ r *
            ∫⁻ ω in {ω : ℕ → EuclideanSpace ℝ (Fin d) | ρ ≤ dist (∑ i : Fin n, wAt W n ω i) 1},
              ‖f (ω 0)‖ₑ ^ r ∂(xLaw μ) := by
          rw [lintegral_add_left (hhm.const_mul _), lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            lintegral_const_mul' _ _ hDtop, lintegral_indicator (hAm n)]
      _ ≤ ENNReal.ofReal ρ * ∫⁻ x, ‖f x‖ₑ ^ r ∂μ + ENNReal.ofReal ρ := by
          rw [hhi]; exact add_le_add le_rfl hn
      _ = (∫⁻ x, ‖f x‖ₑ ^ r ∂μ + 1) * ENNReal.ofReal ρ := by ring
  have hc1 : (2:ℝ≥0∞) ^ (r - 1) ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg (by linarith) (by norm_num)
  have hc2 : ENNReal.ofReal D ^ (r - 1) ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg (by linarith) ENNReal.ofReal_ne_top
  have hlim : Tendsto (fun n => (2:ℝ≥0∞) ^ (r - 1) * (ENNReal.ofReal D ^ (r - 1) *
      (∫⁻ ω, ∑ i : Fin n, ‖wAt W n ω i‖ₑ * ‖f (ω (i.val + 1)) - f (ω 0)‖ₑ ^ r ∂(xLaw μ)) +
      ∫⁻ ω, ‖∑ i : Fin n, wAt W n ω i - 1‖ₑ ^ r * ‖f (ω 0)‖ₑ ^ r ∂(xLaw μ))) atTop (𝓝 0) := by
    have := ENNReal.Tendsto.const_mul ((ENNReal.Tendsto.const_mul hS1 (Or.inr hc2)).add hS2)
      (Or.inr hc1)
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall (fun n => zero_le)) ?_
  filter_upwards [eventually_ge_atTop 1] with n hn1
  have hmS : Measurable (fun ω : ℕ → EuclideanSpace ℝ (Fin d) =>
      ∑ i : Fin n, ‖wAt W n ω i‖ₑ * ‖f (ω (i.val + 1)) - f (ω 0)‖ₑ ^ r) := by
    refine Finset.measurable_sum _ (fun i _ => ((hmw n i).enorm).mul ?_)
    exact (((hf.comp (measurable_pi_apply (i.val + 1))).sub
      (hf.comp (measurable_pi_apply 0))).enorm).pow_const r
  calc ∫⁻ ω, ‖∑ i : Fin n, wAt W n ω i * f (ω (i.val + 1)) - f (ω 0)‖ₑ ^ r ∂(xLaw μ)
      ≤ ∫⁻ ω, (2:ℝ≥0∞) ^ (r - 1) * (ENNReal.ofReal D ^ (r - 1) *
        (∑ i : Fin n, ‖wAt W n ω i‖ₑ * ‖f (ω (i.val + 1)) - f (ω 0)‖ₑ ^ r) +
        ‖∑ i : Fin n, wAt W n ω i - 1‖ₑ ^ r * ‖f (ω 0)‖ₑ ^ r) ∂(xLaw μ) := by
        refine lintegral_mono_ae ?_
        filter_upwards [hD n hn1] with ω hω
        have e : ∑ i : Fin n, wAt W n ω i * f (ω (i.val + 1)) - f (ω 0) =
            ∑ i : Fin n, wAt W n ω i * (f (ω (i.val + 1)) - f (ω 0)) +
              (∑ i : Fin n, wAt W n ω i - 1) * f (ω 0) := by
          simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
          ring
        have hu : ‖∑ i : Fin n, wAt W n ω i * (f (ω (i.val + 1)) - f (ω 0))‖ₑ ≤
            ∑ i : Fin n, ‖wAt W n ω i‖ₑ * ‖f (ω (i.val + 1)) - f (ω 0)‖ₑ := by
          refine (enorm_sum_le _ _).trans (le_of_eq ?_)
          refine Finset.sum_congr rfl (fun i _ => ?_)
          exact enorm_mul _ _
        have hsw : ∑ i : Fin n, ‖wAt W n ω i‖ₑ ≤ ENNReal.ofReal D := by
          have e2 : ∑ i : Fin n, ‖wAt W n ω i‖ₑ = ENNReal.ofReal (∑ i : Fin n, |wAt W n ω i|) := by
            rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => abs_nonneg _)]
            simp [Real.enorm_eq_ofReal_abs]
          rw [e2]; exact ENNReal.ofReal_le_ofReal hω
        rw [e]
        calc ‖∑ i : Fin n, wAt W n ω i * (f (ω (i.val + 1)) - f (ω 0)) +
              (∑ i : Fin n, wAt W n ω i - 1) * f (ω 0)‖ₑ ^ r
            ≤ (∑ i : Fin n, ‖wAt W n ω i‖ₑ * ‖f (ω (i.val + 1)) - f (ω 0)‖ₑ +
                ‖∑ i : Fin n, wAt W n ω i - 1‖ₑ * ‖f (ω 0)‖ₑ) ^ r := by
              refine ENNReal.rpow_le_rpow ?_ hr0
              refine (enorm_add_le _ _).trans (add_le_add hu (le_of_eq (enorm_mul _ _)))
          _ ≤ (2:ℝ≥0∞) ^ (r - 1) * ((∑ i : Fin n, ‖wAt W n ω i‖ₑ * ‖f (ω (i.val + 1)) - f (ω 0)‖ₑ) ^ r
                + (‖∑ i : Fin n, wAt W n ω i - 1‖ₑ * ‖f (ω 0)‖ₑ) ^ r) :=
              ENNReal.rpow_add_le_mul_rpow_add_rpow _ _ hr
          _ ≤ _ := by
              refine mul_le_mul_of_nonneg_left (add_le_add ?_ (le_of_eq
                (ENNReal.mul_rpow_of_nonneg _ _ hr0))) (by positivity)
              refine (p5_jensen r hr _ _).trans ?_
              refine mul_le_mul_of_nonneg_right ?_ (by positivity)
              exact ENNReal.rpow_le_rpow hsw (by linarith)
    _ = _ := by
        rw [lintegral_const_mul' _ _ hc1, lintegral_add_left (hmS.const_mul _),
          lintegral_const_mul' _ _ hc2]

end StoneRegression.Criterion

open StoneRegression.Criterion


theorem solution {d : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ]
    (W : WeightSeq d) (hW : MeasurableWeights W)
    (h1 : ∃ C : ℝ≥0, 1 ≤ C ∧ Cond1 μ W C) (h2 : ∃ D : ℝ, 1 ≤ D ∧ Cond2 μ W D) (h3 : Cond3 μ W)
    (h4 : Cond4 μ W)
    (r : ℝ) (hr : 1 ≤ r) (f : EuclideanSpace ℝ (Fin d) → ℝ) (hf : Measurable f)
    (hfr : ∫⁻ x, ‖f x‖ₑ ^ r ∂μ < ∞) :
    Tendsto (fun n => ∫⁻ ω,
        ‖∑ i : Fin n, wAt W n ω i * f (ω (i.val + 1)) - f (ω 0)‖ₑ ^ r ∂(xLaw μ)) atTop (𝓝 0) := by
  exact p5_core μ W hW h1 h2 h3 h4 r hr f hf hfr
