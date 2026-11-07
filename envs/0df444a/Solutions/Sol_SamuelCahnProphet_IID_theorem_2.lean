-- Prove2me | solution 1 for SamuelCahnProphet.IID.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T14:07:38.72645+00:00
-- url     : https://prove2.me/submissions/4ddf7a00-d7bf-469e-856a-7c29406d3228

import Mathlib
import Definitions.Def_SamuelCahnProphet_IID_Setting
import Theorems.Thm_SamuelCahnProphet_IID_upper_bound
import Theorems.Thm_SamuelCahnProphet_IID_tendsto_ratio_Q
import Theorems.Thm_SamuelCahnProphet_IID_tendsto_Q_two
import Theorems.Thm_SamuelCahnProphet_IID_aStarIID_spec

open MeasureTheory Filter Topology
open SamuelCahnProphet.IID

lemma scp2_threePoint_prob (n a b c : ℝ) (hn : 0 < n) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hbc : b + c ≤ n) : IsProbabilityMeasure (threePoint n a b c) := by
  constructor
  simp only [threePoint, Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  have h1 : 0 ≤ 1 - (b + c) / n := by
    rw [sub_nonneg, div_le_one hn]; exact hbc
  rw [← ENNReal.ofReal_add h1 (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity)]
  rw [show 1 - (b + c) / n + c / n + b / n = 1 by field_simp; ring]
  simp

lemma scp2_threePoint_Iio (n a b c : ℝ) (ha : 0 < a) :
    threePoint n a b c (Set.Iio 0) = 0 := by
  simp only [threePoint, Measure.add_apply, Measure.smul_apply, smul_eq_mul,
    Measure.dirac_apply' _ measurableSet_Iio]
  simp [Set.indicator, ha.not_gt]

theorem solution :
    (∀ (n : ℕ) [NeZero n] (μ : Measure ℝ) [IsProbabilityMeasure μ], μ (Set.Iio 0) = 0 →
        Emax μ n ≤ 2 * supEplus μ n) ∧
      (∀ (n : ℕ) [NeZero n] (μ : Measure ℝ), supEplus μ n ≤ supE μ n) ∧
      (∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (μ : Measure ℝ), IsProbabilityMeasure μ ∧ μ (Set.Iio 0) = 0 ∧
        ENNReal.ofReal (2 - ε) * supE μ (n + 1) < Emax μ (n + 1)) := by
  refine ⟨fun n _ μ _ hμ => upper_bound n μ hμ, ?_, ?_⟩
  · intro n _ μ
    refine iSup₂_mono fun c _ => max_le_max ?_ ?_
    · refine lintegral_mono fun x => ?_
      split_ifs <;> simp
    · refine lintegral_mono fun x => ?_
      split_ifs <;> simp
  · intro ε hε
    -- choose b, c with Q b c > max (2 - ε) 0
    have hQ := tendsto_Q_two
    have hev1 : ∀ᶠ p : ℝ × ℝ in (𝓝[>] (0 : ℝ)) ×ˢ atTop, max (2 - ε) 0 < Q p.1 p.2 :=
      hQ.eventually (lt_mem_nhds (by apply max_lt <;> linarith))
    have hev2 : ∀ᶠ p : ℝ × ℝ in (𝓝[>] (0 : ℝ)) ×ˢ atTop, 0 < p.1 ∧ 0 < p.2 :=
      prod_mem_prod self_mem_nhdsWithin (Ioi_mem_atTop 0)
    obtain ⟨⟨b, c⟩, hQbc, hb, hc⟩ := (hev1.and hev2).exists
    simp only at hQbc hb hc
    have hr := tendsto_ratio_Q b c hb hc
    have hev3 := hr.eventually (lt_mem_nhds hQbc)
    have hev4 : ∀ᶠ k : ℕ in atTop, b + c < ((k + 1 : ℕ) : ℝ) := by
      obtain ⟨N, hN⟩ := exists_nat_gt (b + c)
      filter_upwards [eventually_ge_atTop N] with k hk
      have : (N : ℝ) ≤ k := by exact_mod_cast hk
      push_cast; linarith
    obtain ⟨k, hk, hkbc⟩ := (hev3.and hev4).exists
    obtain ⟨ha0, ha1⟩ := (aStarIID_spec b c hb hc).2
    set μ := threePoint ((k + 1 : ℕ) : ℝ) (aStarIID b c) b c with hμ
    have hprob : IsProbabilityMeasure μ :=
      scp2_threePoint_prob _ _ _ _ (by positivity) hb.le hc.le hkbc.le
    refine ⟨k, μ, hprob, scp2_threePoint_Iio _ _ _ _ ha0, ?_⟩
    set A := (Emax μ (k + 1)).toReal
    set B := (supE μ (k + 1)).toReal
    have hk' : max (2 - ε) 0 < A / B := hk
    have hpos : 0 < A / B := lt_of_le_of_lt (le_max_right _ _) hk'
    have hA0 : 0 ≤ A := ENNReal.toReal_nonneg
    have hB0 : 0 ≤ B := ENNReal.toReal_nonneg
    have hBpos : 0 < B := by
      rcases hB0.eq_or_lt with h | h
      · rw [← h, div_zero] at hpos; exact absurd hpos (lt_irrefl _)
      · exact h
    have hApos : 0 < A := by
      rcases hA0.eq_or_lt with h | h
      · rw [← h, zero_div] at hpos; exact absurd hpos (lt_irrefl _)
      · exact h
    have hAne : Emax μ (k + 1) ≠ ⊤ := fun h => by
      have : A = 0 := by simp [A, h]
      linarith
    have hBne : supE μ (k + 1) ≠ ⊤ := fun h => by
      have : B = 0 := by simp [B, h]
      linarith
    have hAeq : Emax μ (k + 1) = ENNReal.ofReal A := (ENNReal.ofReal_toReal hAne).symm
    have hBeq : supE μ (k + 1) = ENNReal.ofReal B := (ENNReal.ofReal_toReal hBne).symm
    rw [hAeq, hBeq, ← ENNReal.ofReal_mul' hB0, ENNReal.ofReal_lt_ofReal_iff hApos]
    have := (lt_div_iff₀ hBpos).1 (lt_of_le_of_lt (le_max_left _ _) hk')
    exact this
