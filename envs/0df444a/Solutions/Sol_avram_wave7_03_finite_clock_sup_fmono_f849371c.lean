-- Prove2me | solution 1 for avram_wave7_03_finite_clock_sup_fmono_f849371c
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T17:43:25.10492+00:00
-- url     : https://prove2.me/submissions/8f59fbb2-58e2-47a0-a9ef-d53972a356ef

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_random_upper_clock_complete_stieltjes_cash_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_finite_random_clock_cash_eq_iSup_min_integer_clocks
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_full_ruin_bounded_clock_unconditional_mean_eq
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- The exact source stopped Stieltjes ENNReal cash is monotone along
    the actual natural-number truncations of a measurable random clock. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q)
    (τ : Ω → ℝ≥0)
    (hτMeas : Measurable (fun ω => (τ ω : ℝ)))
    (hDiv : (let θ : ℕ → Ω → ℝ≥0 :=
      (fun n ω => min (τ ω) (((n + 1 : ℕ) : ℝ≥0)));
      let F : ℕ → Ω → ℝ≥0∞ := (fun n ω =>
        ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (θ n ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω));
      IsDividendStrategy 𝓕 D))
    (hθMeas : (let θ : ℕ → Ω → ℝ≥0 :=
      (fun n ω => min (τ ω) (((n + 1 : ℕ) : ℝ≥0)));
      let F : ℕ → Ω → ℝ≥0∞ := (fun n ω =>
        ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (θ n ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω));
      ∀ n : ℕ, Measurable (fun ω => (θ n ω : ℝ))))
    (hFm : (let θ : ℕ → Ω → ℝ≥0 :=
      (fun n ω => min (τ ω) (((n + 1 : ℕ) : ℝ≥0)));
      let F : ℕ → Ω → ℝ≥0∞ := (fun n ω =>
        ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (θ n ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω));
      ∀ n : ℕ, Measurable (F n))) :
    (let θ : ℕ → Ω → ℝ≥0 :=
      (fun n ω => min (τ ω) (((n + 1 : ℕ) : ℝ≥0)));
      let F : ℕ → Ω → ℝ≥0∞ := (fun n ω =>
        ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (θ n ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω));
      Monotone F) := by
  change Monotone (fun n : ℕ => fun ω : Ω =>
    ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
        Iic (((min (τ ω) (((n + 1 : ℕ) : ℝ≥0))) : ℝ≥0) : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω))
  intro n m hnm ω
  apply MeasureTheory.lintegral_mono_set
  intro t ht
  have hnmNN :
      (((n + 1 : ℕ) : ℝ≥0)) ≤ (((m + 1 : ℕ) : ℝ≥0)) := by
    exact_mod_cast Nat.add_le_add_right hnm 1
  have hθNN :
      min (τ ω) (((n + 1 : ℕ) : ℝ≥0)) ≤
        min (τ ω) (((m + 1 : ℕ) : ℝ≥0)) :=
    min_le_min_left (τ ω) hnmNN
  have hθReal :
      ((min (τ ω) (((n + 1 : ℕ) : ℝ≥0))) : ℝ) ≤
        ((min (τ ω) (((m + 1 : ℕ) : ℝ≥0))) : ℝ) := by
    exact_mod_cast hθNN
  exact ⟨ht.1, (Set.mem_Iic.mp ht.2).trans hθReal⟩
