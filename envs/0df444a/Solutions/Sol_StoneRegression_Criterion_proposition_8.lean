-- Prove2me | solution 1 for StoneRegression.Criterion.proposition_8
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T06:30:21.56719+00:00
-- url     : https://prove2.me/submissions/09a24685-2715-474c-9dfe-1e6b35d164a8

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
lemma p8_char {ι : Type*} [Fintype ι] (d : ι → ℝ) :
    ∫ y, Real.cos (∑ k, d k * y k) ∂(Measure.pi (fun _ : ι => gaussianReal 0 1)) =
      Real.exp (-(∑ k, d k ^ 2) / 2) := by
  have h1 : ∀ y : ι → ℝ, Real.cos (∑ k, d k * y k) =
      RCLike.re (∏ k, Complex.exp (↑(d k) * ↑(y k) * Complex.I)) := by
    intro y
    rw [← Complex.exp_sum, ← Complex.exp_ofReal_mul_I_re]
    congr 2
    push_cast
    rw [Finset.sum_mul]
  simp_rw [h1]
  have hint : Integrable (fun y : ι → ℝ => ∏ k, Complex.exp (↑(d k) * ↑(y k) * Complex.I))
      (Measure.pi (fun _ : ι => gaussianReal 0 1)) := by
    refine Integrable.of_bound (C := 1) ?_ ?_
    · refine Continuous.aestronglyMeasurable ?_
      fun_prop
    · refine Eventually.of_forall (fun y => ?_)
      rw [norm_prod]
      refine le_of_eq ?_
      refine Finset.prod_eq_one (fun k _ => ?_)
      rw [← Complex.ofReal_mul, Complex.norm_exp_ofReal_mul_I]
  rw [integral_re hint]
  rw [integral_fintype_prod_eq_prod (f := fun k (x : ℝ) => Complex.exp (↑(d k) * ↑x * Complex.I))]
  have h3 : ∀ k, ∫ x, Complex.exp (↑(d k) * ↑x * Complex.I) ∂(gaussianReal 0 1) =
      Complex.exp (((-(d k ^ 2) / 2 : ℝ) : ℂ)) := by
    intro k
    have := charFun_gaussianReal (μ := 0) (v := 1) (d k)
    rw [charFun_apply_real] at this
    rw [this]
    congr 1
    push_cast
    ring
  simp_rw [h3]
  rw [← Complex.exp_sum, ← Complex.ofReal_sum, ← Complex.ofReal_exp]
  simp only [RCLike.re_to_complex, Complex.ofReal_re]
  congr 1
  rw [← Finset.sum_div, Finset.sum_neg_distrib]


abbrev p8S (n : ℕ) : Finset ℕ := Finset.range (n + 1)

def p8z (n : ℕ) : ↥(p8S n) := ⟨0, by simp [p8S]⟩

def p8e (n : ℕ) (j : Fin n) : ↥(p8S n) := ⟨j.val + 1, by simp [p8S]⟩

lemma p8_inner (n : ℕ) (c : Fin n → ℝ) :
    ∫⁻ y, ENNReal.ofReal (1 - Real.cos (∑ i : Fin n, c i * y (p8e n i)))
      ∂(Measure.pi (fun _ : ↥(p8S n) => gaussianReal 0 1)) =
      ENNReal.ofReal (1 - Real.exp (-(∑ i : Fin n, c i ^ 2) / 2)) := by
  let d : ↥(p8S n) → ℝ := fun k => if h : 1 ≤ k.val then
    c ⟨k.val - 1, by have := k.2; simp only [p8S, Finset.mem_range] at this; omega⟩ else 0
  have hde : ∀ i, d (p8e n i) = c i := by
    intro i
    simp only [d, p8e]
    rw [dif_pos (by omega)]
    congr 1
  have hrange : ∀ k ∉ Set.range (p8e n), d k = 0 := by
    intro k hk
    by_contra hne
    simp only [d] at hne
    split_ifs at hne with h
    · have hk2 := k.2
      simp only [p8S, Finset.mem_range] at hk2
      exact hk ⟨⟨k.val - 1, by omega⟩, Subtype.ext (by simp [p8e]; omega)⟩
    · exact hne rfl
  have hinj : Function.Injective (p8e n) := by
    intro i j h
    simp only [p8e, Subtype.mk.injEq] at h
    exact Fin.ext (by omega)
  have hsum1 : ∀ y : ↥(p8S n) → ℝ, ∑ i : Fin n, c i * y (p8e n i) = ∑ k, d k * y k := fun y =>
    Fintype.sum_of_injective (p8e n) hinj _ _ (fun k hk => by rw [hrange k hk, zero_mul])
      (fun i => by rw [hde])
  have hsum2 : ∑ i : Fin n, c i ^ 2 = ∑ k, d k ^ 2 :=
    Fintype.sum_of_injective (p8e n) hinj _ _ (fun k hk => by rw [hrange k hk]; ring)
      (fun i => by rw [hde])
  simp_rw [hsum1]
  rw [hsum2, ← p8_char d]
  have hcos : Integrable (fun y : ↥(p8S n) → ℝ => Real.cos (∑ k, d k * y k))
      (Measure.pi (fun _ : ↥(p8S n) => gaussianReal 0 1)) := by
    refine Integrable.of_bound (C := 1) ?_ ?_
    · exact Continuous.aestronglyMeasurable (by fun_prop)
    · exact Eventually.of_forall (fun y => by rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _)
  have hint : Integrable (fun y : ↥(p8S n) → ℝ => 1 - Real.cos (∑ k, d k * y k))
      (Measure.pi (fun _ : ↥(p8S n) => gaussianReal 0 1)) := (integrable_const 1).sub hcos
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (Eventually.of_forall (fun y => by simp only [Pi.zero_apply]; linarith [Real.cos_le_one (∑ k, d k * y k)])),
    integral_sub (integrable_const 1) hcos]
  simp

lemma p8_meas_est {d : ℕ} (W : WeightSeq d) (hW : MeasurableWeights W) (n : ℕ) :
    Measurable (fun ω : ℕ → EuclideanSpace ℝ (Fin d) × ℝ => estimate W n ω) := by
  unfold estimate
  refine Finset.measurable_sum _ (fun i _ => ?_)
  have hp : Measurable (fun ω : ℕ → EuclideanSpace ℝ (Fin d) × ℝ =>
      ((ω 0).1, fun j : Fin n => (ω (j.val + 1)).1)) :=
    (measurable_pi_apply 0).fst.prodMk (measurable_pi_lambda _ (fun j => (measurable_pi_apply _).fst))
  exact ((measurable_pi_apply i).comp ((hW n).comp hp)).mul (measurable_pi_apply _).snd

lemma p8_B {d : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ]
    (W : WeightSeq d) (hW : MeasurableWeights W) (n : ℕ) :
    ∫⁻ ω, ENNReal.ofReal (1 - Real.cos (estimate W n ω))
      ∂(pairLaw μ (Kernel.const (EuclideanSpace ℝ (Fin d)) (gaussianReal 0 1))) =
    ∫⁻ ω, ENNReal.ofReal (1 - Real.exp (-(∑ i : Fin n, wAt W n ω i ^ 2) / 2)) ∂(xLaw μ) := by
  let G : (↥(p8S n) → EuclideanSpace ℝ (Fin d) × ℝ) → ℝ≥0∞ := fun z =>
    ENNReal.ofReal (1 - Real.cos (∑ i : Fin n,
      W n (z (p8z n)).1 (fun j => (z (p8e n j)).1) i * (z (p8e n i)).2))
  let H : (↥(p8S n) → EuclideanSpace ℝ (Fin d)) → ℝ≥0∞ := fun x =>
    ENNReal.ofReal (1 - Real.exp (-(∑ i : Fin n, W n (x (p8z n)) (fun j => x (p8e n j)) i ^ 2) / 2))
  have hA : ∀ i : Fin n, Measurable (fun z : ↥(p8S n) → EuclideanSpace ℝ (Fin d) × ℝ =>
      W n (z (p8z n)).1 (fun j => (z (p8e n j)).1) i) := fun i =>
    (measurable_pi_apply i).comp ((hW n).comp (((measurable_pi_apply (p8z n)).fst).prodMk
      (measurable_pi_lambda _ (fun j => (measurable_pi_apply (p8e n j)).fst))))
  have hG : Measurable G := ENNReal.measurable_ofReal.comp (measurable_const.sub
    (Real.measurable_cos.comp (Finset.measurable_sum _
      (fun i _ => (hA i).mul (measurable_pi_apply (p8e n i)).snd))))
  have hB : ∀ i : Fin n, Measurable (fun x : ↥(p8S n) → EuclideanSpace ℝ (Fin d) =>
      W n (x (p8z n)) (fun j => x (p8e n j)) i) := by
    intro i
    have hp : Measurable (fun x : ↥(p8S n) → EuclideanSpace ℝ (Fin d) =>
        (x (p8z n), fun j : Fin n => x (p8e n j))) :=
      (measurable_pi_apply _).prodMk (measurable_pi_lambda _ (fun j => measurable_pi_apply _))
    exact (measurable_pi_apply i).comp ((hW n).comp hp)
  have hH : Measurable H := ENNReal.measurable_ofReal.comp (measurable_const.sub
    (Real.measurable_exp.comp (((Finset.measurable_sum _
      (fun i _ => (hB i).pow_const 2)).neg).div_const _)))
  have e1 : ∫⁻ ω, ENNReal.ofReal (1 - Real.cos (estimate W n ω))
      ∂(pairLaw μ (Kernel.const (EuclideanSpace ℝ (Fin d)) (gaussianReal 0 1))) =
      ∫⁻ ω, G ((p8S n).restrict ω)
      ∂(pairLaw μ (Kernel.const (EuclideanSpace ℝ (Fin d)) (gaussianReal 0 1))) := rfl
  have e2 : ∫⁻ ω, ENNReal.ofReal (1 - Real.exp (-(∑ i : Fin n, wAt W n ω i ^ 2) / 2)) ∂(xLaw μ) =
      ∫⁻ ω, H ((p8S n).restrict ω) ∂(xLaw μ) := rfl
  rw [e1, e2]
  unfold pairLaw xLaw
  have k1 := lintegral_restrict_infinitePi (X := fun _ : ℕ => EuclideanSpace ℝ (Fin d) × ℝ)
    (μ := fun _ => μ ⊗ₘ Kernel.const (EuclideanSpace ℝ (Fin d)) (gaussianReal 0 1)) (s := p8S n) hG
  have k2 := lintegral_restrict_infinitePi (X := fun _ : ℕ => EuclideanSpace ℝ (Fin d))
    (μ := fun _ => μ) (s := p8S n) hH
  refine k1.trans (Eq.trans ?_ k2.symm)
  rw [Measure.compProd_const]
  have hmp := measurePreserving_arrowProdEquivProdArrow (EuclideanSpace ℝ (Fin d)) ℝ ↥(p8S n)
    (fun _ => μ) (fun _ => gaussianReal 0 1)
  rw [← (MeasurePreserving.symm _ hmp).lintegral_comp hG,
    lintegral_prod (fun a => G ((MeasurableEquiv.arrowProdEquivProdArrow
      (EuclideanSpace ℝ (Fin d)) ℝ ↥(p8S n)).symm a))
      (by exact (hG.comp (MeasurableEquiv.measurable _)).aemeasurable)]
  congr 1
  ext x
  exact p8_inner n (fun i => W n (x (p8z n)) (fun j => x (p8e n j)) i)

lemma p8_cos_le (x : ℝ) : |1 - Real.cos x| ≤ |x| := by
  rw [abs_of_nonneg (by linarith [Real.cos_le_one x])]
  by_cases hx : 2 ≤ |x|
  · linarith [Real.neg_one_le_cos x]
  · have h1 := Real.one_sub_sq_div_two_le_cos (x := x)
    have h2 : x ^ 2 = |x| ^ 2 := (sq_abs x).symm
    push_neg at hx
    nlinarith [abs_nonneg x]

theorem p8_core {d : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ]
    (W : WeightSeq d) (hW : MeasurableWeights W)
    (hY : TendstoInMeasure (pairLaw μ (Kernel.const (EuclideanSpace ℝ (Fin d)) (gaussianReal 0 1)))
      (fun n ω => estimate W n ω) atTop (fun _ => 0)) :
    TendstoInMeasure (xLaw μ) (fun n ω => ∑ i : Fin n, wAt W n ω i ^ 2) atTop (fun _ => 0) := by
  have : IsProbabilityMeasure
      (pairLaw μ (Kernel.const (EuclideanSpace ℝ (Fin d)) (gaussianReal 0 1))) := by
    unfold pairLaw; infer_instance
  have hA := p1_l1 (pairLaw μ (Kernel.const (EuclideanSpace ℝ (Fin d)) (gaussianReal 0 1)))
    (fun n ω => 1 - Real.cos (estimate W n ω))
    (fun n => measurable_const.sub (Real.measurable_cos.comp (p8_meas_est W hW n))) 2
    (Eventually.of_forall (fun n => ae_of_all _ (fun ω =>
      ⟨by linarith [Real.cos_le_one (estimate W n ω)],
       by linarith [Real.neg_one_le_cos (estimate W n ω)]⟩))) (by
      rw [tendstoInMeasure_iff_dist] at hY ⊢
      intro ε hε
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hY ε hε)
        (fun n => zero_le) (fun n => measure_mono (fun ω hω => ?_))
      change ε ≤ dist _ 0 at hω
      change ε ≤ dist _ 0
      rw [Real.dist_eq, sub_zero] at hω ⊢
      exact hω.trans (p8_cos_le _))
  simp only [p8_B μ W hW] at hA
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  have hc : 0 < 1 - Real.exp (-ε / 2) := by
    have : Real.exp (-ε / 2) < 1 := Real.exp_lt_one_iff.2 (by linarith)
    linarith
  have hB := ENNReal.Tendsto.div_const hA (Or.inr (ENNReal.ofReal_pos.2 hc).ne')
  rw [ENNReal.zero_div] at hB
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hB
    (fun n => zero_le) (fun n => ?_)
  have hmS : Measurable (fun ω : ℕ → EuclideanSpace ℝ (Fin d) =>
      ENNReal.ofReal (1 - Real.exp (-(∑ i : Fin n, wAt W n ω i ^ 2) / 2))) :=
    ENNReal.measurable_ofReal.comp (measurable_const.sub (Real.measurable_exp.comp
      (((Finset.measurable_sum _ (fun i _ => (p1_meas_wAt W hW n i).pow_const 2)).neg).div_const _)))
  calc xLaw μ {ω | ε ≤ dist (∑ i : Fin n, wAt W n ω i ^ 2) 0}
      ≤ xLaw μ {ω | ENNReal.ofReal (1 - Real.exp (-ε / 2)) ≤
          ENNReal.ofReal (1 - Real.exp (-(∑ i : Fin n, wAt W n ω i ^ 2) / 2))} := by
        refine measure_mono (fun ω hω => ?_)
        change ε ≤ dist _ 0 at hω
        change ENNReal.ofReal _ ≤ ENNReal.ofReal _
        rw [Real.dist_eq, sub_zero] at hω
        refine ENNReal.ofReal_le_ofReal ?_
        have : Real.exp (-(∑ i : Fin n, wAt W n ω i ^ 2) / 2) ≤ Real.exp (-ε / 2) := by
          refine Real.exp_le_exp.2 ?_
          have := le_trans hω (le_of_eq (abs_of_nonneg
            (Finset.sum_nonneg (fun i _ => sq_nonneg (wAt W n ω i)))))
          linarith
        linarith
    _ ≤ (∫⁻ ω, ENNReal.ofReal (1 - Real.exp (-(∑ i : Fin n, wAt W n ω i ^ 2) / 2)) ∂(xLaw μ)) /
          ENNReal.ofReal (1 - Real.exp (-ε / 2)) :=
        meas_ge_le_lintegral_div hmS.aemeasurable (ENNReal.ofReal_pos.2 hc).ne' ENNReal.ofReal_ne_top

end StoneRegression.Criterion

open StoneRegression.Criterion


theorem solution {d : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ]
    (W : WeightSeq d) (hW : MeasurableWeights W)
    (hY : TendstoInMeasure (pairLaw μ (Kernel.const (EuclideanSpace ℝ (Fin d)) (gaussianReal 0 1)))
      (fun n ω => estimate W n ω) atTop (fun _ => 0)) :
    TendstoInMeasure (xLaw μ) (fun n ω => ∑ i : Fin n, wAt W n ω i ^ 2) atTop (fun _ => 0) := by
  exact p8_core μ W hW hY
