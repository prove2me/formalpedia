-- Prove2me | solution 1 for avram_p4_f_assembly_original_compact_band_paid_resid_pointwise_upper_bound_a9c704b6
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T08:09:06.759236+00:00
-- url     : https://prove2.me/submissions/161f0701-af89-40ea-8e2f-8df9b1791740

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_ubv_C2_interior_band_secant_lipschitz
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_countable_rightjump_local_secant_summable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (w : ℝ → ℝ) (q : ℝ)
    (C : ℝ≥0∞)
    (hwC2 : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ)
    (hOpen : IsOpen {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hBand : Icc a b ⊆ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (K : ℝ≥0)
    (hDeriv : ∀ y ∈ Icc a b, ‖deriv w y‖₊ ≤ K)
    (hjump : ∀ ω (u : ℝ≥0),
      (u = 0 ∨ (u : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D u ω - D u ω ≤
        w (riskProcess X x D u ω) -
          w (riskProcess X x D u ω -
            (rightLimit D u ω - D u ω)))
    {ι : Type*} (t : ι → ℝ≥0) (ω : Ω)
    (hPre : ∀ i : ι, t i = 0 ∨
      (t i : ℝ≥0∞) < ruinTime X x D ω)
    (hPreBand : ∀ i : ι,
      riskProcess X x D (t i) ω ∈ Icc a b)
    (hPostBand : ∀ i : ι,
      x + X.X (t i) ω - rightLimit D (t i) ω ∈ Icc a b)
    (hPayNonneg : ∀ i : ι,
      0 ≤ rightLimit D (t i) ω - D (t i) ω)
    (hPaySummable : Summable (fun i : ι =>
      Real.exp (-(q * (t i : ℝ))) *
        (rightLimit D (t i) ω - D (t i) ω))) 
    : ∀ i : ι,
      w (riskProcess X x D (t i) ω) -
        w (x + X.X (t i) ω - rightLimit D (t i) ω) ≤
      max 1 (K : ℝ) * (rightLimit D (t i) ω - D (t i) ω) := by
    have hLip :=
        avram_p4_d_dividend_ubv_C2_interior_band_secant_lipschitz
          C w hwC2 a b hOpen hBand K hDeriv
    intro i
    have hGap :
        riskProcess X x D (t i) ω -
          (x + X.X (t i) ω - rightLimit D (t i) ω) =
        rightLimit D (t i) ω - D (t i) ω := by
      simp only [riskProcess]
      ring
    calc
      w (riskProcess X x D (t i) ω) -
          w (x + X.X (t i) ω - rightLimit D (t i) ω)
          ≤ |w (riskProcess X x D (t i) ω) -
              w (x + X.X (t i) ω - rightLimit D (t i) ω)| :=
            le_abs_self _
      _ ≤ (K : ℝ) *
          |riskProcess X x D (t i) ω -
            (x + X.X (t i) ω - rightLimit D (t i) ω)| :=
            hLip _ (hPreBand i) _ (hPostBand i)
      _ = (K : ℝ) *
          (rightLimit D (t i) ω - D (t i) ω) := by
            rw [hGap, abs_of_nonneg (hPayNonneg i)]
      _ ≤ max 1 (K : ℝ) *
          (rightLimit D (t i) ω - D (t i) ω) :=
            mul_le_mul_of_nonneg_right (le_max_right 1 (K : ℝ))
              (hPayNonneg i)
end
