-- Prove2me | solution 1 for avram_wave7_03_finite_clock_sup_measurability_b87ef32a
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T17:42:33.564311+00:00
-- url     : https://prove2.me/submissions/61a5acc8-9577-4e09-b1fc-b3a6e3665af5

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

/-- Every finite natural-number truncation of the actual random clock is
    a measurable real-valued clock, with no process replacement. -/
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
      IsDividendStrategy 𝓕 D)) :
    (let θ : ℕ → Ω → ℝ≥0 :=
      (fun n ω => min (τ ω) (((n + 1 : ℕ) : ℝ≥0)));
      ∀ n : ℕ, Measurable (fun ω => (θ n ω : ℝ))) := by
  change ∀ n : ℕ,
    Measurable (fun ω : Ω =>
      ((min (τ ω) (((n + 1 : ℕ) : ℝ≥0))) : ℝ))
  intro n
  have hEq :
      (fun ω : Ω => ((min (τ ω) (((n + 1 : ℕ) : ℝ≥0))) : ℝ)) =
        (fun ω : Ω => min (τ ω : ℝ) (((n + 1 : ℕ) : ℝ))) := by
    funext ω
    simp only [NNReal.coe_min, NNReal.coe_natCast]
  rw [hEq]
  exact hτMeas.min measurable_const
