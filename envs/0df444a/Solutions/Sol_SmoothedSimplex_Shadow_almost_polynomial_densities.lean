-- Prove2me | solution 1 for SmoothedSimplex.Shadow.almost_polynomial_densities
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T22:22:30.869169+00:00
-- url     : https://prove2.me/submissions/c20466d4-afd7-418f-85bb-225584746873

import Mathlib

open MeasureTheory ProbabilityTheory in
theorem apd_key_6b955179 (k : ℝ) (hk : 0 < k) (a : ℝ) (ha : 0 ≤ a) :
    ∫⁻ t in Set.Ioc 0 a, ENNReal.ofReal (t ^ k) = ENNReal.ofReal (a ^ (k + 1) / (k + 1)) := by
  have hint : IntervalIntegrable (fun x : ℝ => x ^ k) volume 0 a :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · rw [← intervalIntegral.integral_of_le ha, integral_rpow (Or.inl (by linarith)),
      Real.zero_rpow (by linarith), sub_zero]
  · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le ha).1 hint
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact Real.rpow_nonneg ht.1.le k

open MeasureTheory ProbabilityTheory in
open scoped RealInnerProductSpace in
theorem solution (μ : ℝ → ℝ) (hμm : Measurable μ) (hμ0 : ∀ t, 0 ≤ μ t)
    (k : ℝ) (hk : 0 < k) (t₀ c : ℝ) (ht₀ : 0 < t₀)
    (hpos : ∀ t ∈ Set.Icc 0 t₀, 0 < μ t)
    (hc : ∀ t ∈ Set.Icc 0 t₀, ∀ t' ∈ Set.Icc 0 t₀, μ t ≤ c * μ t') (ε : ℝ) :
    ∫⁻ t in Set.Ico 0 ε, ENNReal.ofReal (μ t * t ^ k) ≤
      ENNReal.ofReal (c * (ε / t₀) ^ (k + 1)) *
        ∫⁻ t in Set.Ici 0, ENNReal.ofReal (μ t * t ^ k) := by
  have h0 : (0 : ℝ) ∈ Set.Icc 0 t₀ := ⟨le_rfl, ht₀.le⟩
  have hμ00 := hpos 0 h0
  have hc1 : 1 ≤ c := by
    have := hc 0 h0 0 h0
    nlinarith
  have hcpos : 0 < c := by linarith
  rcases le_or_gt ε 0 with hε | hε
  · rw [Set.Ico_eq_empty (by linarith)]
    simp
  rcases le_or_gt t₀ ε with hεt | hεt
  · calc ∫⁻ t in Set.Ico 0 ε, ENNReal.ofReal (μ t * t ^ k)
          ≤ ∫⁻ t in Set.Ici 0, ENNReal.ofReal (μ t * t ^ k) :=
            lintegral_mono_set Set.Ico_subset_Ici_self
      _ = 1 * ∫⁻ t in Set.Ici 0, ENNReal.ofReal (μ t * t ^ k) := (one_mul _).symm
      _ ≤ _ := by
          gcongr
          rw [ENNReal.one_le_ofReal]
          exact one_le_mul_of_one_le_of_one_le hc1
            (Real.one_le_rpow ((one_le_div ht₀).2 hεt) (by linarith))
  -- main case 0 < ε < t₀
  set m := sInf (μ '' Set.Icc 0 t₀) with hm
  have hne : (μ '' Set.Icc 0 t₀).Nonempty := ⟨μ 0, 0, h0, rfl⟩
  have hbdd : BddBelow (μ '' Set.Icc 0 t₀) := ⟨0, by rintro _ ⟨x, -, rfl⟩; exact hμ0 x⟩
  have hm_le : ∀ s ∈ Set.Icc 0 t₀, m ≤ μ s := fun s hs => csInf_le hbdd ⟨s, hs, rfl⟩
  have hm_nn : 0 ≤ m := le_csInf hne (by rintro _ ⟨x, -, rfl⟩; exact hμ0 x)
  have hupper : ∀ t ∈ Set.Icc 0 t₀, μ t ≤ c * m := by
    intro t ht
    have : μ t / c ≤ m := le_csInf hne (by
      rintro _ ⟨s, hs, rfl⟩
      rw [div_le_iff₀ hcpos]
      linarith [hc t ht s hs])
    rw [div_le_iff₀ hcpos] at this
    linarith
  have hL : ∫⁻ t in Set.Ico 0 ε, ENNReal.ofReal (μ t * t ^ k) ≤
      ENNReal.ofReal (c * m) * ENNReal.ofReal (ε ^ (k + 1) / (k + 1)) := by
    calc ∫⁻ t in Set.Ico 0 ε, ENNReal.ofReal (μ t * t ^ k)
          ≤ ∫⁻ t in Set.Icc 0 ε, ENNReal.ofReal (μ t * t ^ k) :=
            lintegral_mono_set Set.Ico_subset_Icc_self
      _ = ∫⁻ t in Set.Ioc 0 ε, ENNReal.ofReal (μ t * t ^ k) :=
            setLIntegral_congr Ioc_ae_eq_Icc.symm
      _ ≤ ∫⁻ t in Set.Ioc 0 ε, ENNReal.ofReal (c * m) * ENNReal.ofReal (t ^ k) := by
            apply setLIntegral_mono' measurableSet_Ioc
            intro t ht
            rw [← ENNReal.ofReal_mul (by positivity)]
            apply ENNReal.ofReal_le_ofReal
            have h1 := hupper t ⟨ht.1.le, by linarith [ht.2]⟩
            have h2 := Real.rpow_nonneg ht.1.le k
            nlinarith
      _ = _ := by
            rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, apd_key_6b955179 k hk ε hε.le]
  have hR : ENNReal.ofReal m * ENNReal.ofReal (t₀ ^ (k + 1) / (k + 1)) ≤
      ∫⁻ t in Set.Ici 0, ENNReal.ofReal (μ t * t ^ k) := by
    calc ENNReal.ofReal m * ENNReal.ofReal (t₀ ^ (k + 1) / (k + 1))
          = ∫⁻ t in Set.Ioc 0 t₀, ENNReal.ofReal m * ENNReal.ofReal (t ^ k) := by
            rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, apd_key_6b955179 k hk t₀ ht₀.le]
      _ ≤ ∫⁻ t in Set.Ioc 0 t₀, ENNReal.ofReal (μ t * t ^ k) := by
            apply setLIntegral_mono' measurableSet_Ioc
            intro t ht
            rw [← ENNReal.ofReal_mul hm_nn]
            apply ENNReal.ofReal_le_ofReal
            have h1 := hm_le t ⟨ht.1.le, ht.2⟩
            have h2 := Real.rpow_nonneg ht.1.le k
            nlinarith
      _ ≤ _ := lintegral_mono_set (Set.Ioc_subset_Ioi_self.trans Set.Ioi_subset_Ici_self)
  calc ∫⁻ t in Set.Ico 0 ε, ENNReal.ofReal (μ t * t ^ k)
        ≤ ENNReal.ofReal (c * m) * ENNReal.ofReal (ε ^ (k + 1) / (k + 1)) := hL
    _ = ENNReal.ofReal (c * (ε / t₀) ^ (k + 1)) *
          (ENNReal.ofReal m * ENNReal.ofReal (t₀ ^ (k + 1) / (k + 1))) := by
        have hk1 : 0 < k + 1 := by linarith
        have ht0k : 0 < t₀ ^ (k + 1) := Real.rpow_pos_of_pos ht₀ _
        have hεk : 0 ≤ ε ^ (k + 1) := Real.rpow_nonneg hε.le _
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hm_nn,
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [Real.div_rpow hε.le ht₀.le]
        field_simp
    _ ≤ _ := by gcongr
