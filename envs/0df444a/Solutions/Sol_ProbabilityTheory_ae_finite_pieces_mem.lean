-- Prove2me | solution 1 for ProbabilityTheory.ae_finite_pieces_mem
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T10:32:10.453346+00:00
-- url     : https://prove2.me/submissions/a036fffc-7290-4db1-81c8-528a496243c2

import Definitions.Def_LeanLevy_RandomMeasure_TimeSpacePoisson
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Set Topology Complex
open scoped NNReal ENNReal BigOperators
variable {Ω : Type} [MeasurableSpace Ω] {ν : Measure ℝ} [SigmaFinite ν]
  {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → ℝ × ℝ} {μ : Measure Ω}

theorem solution [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X ((volume : Measure ℝ).prod ν) μ)
    {R : Set (ℝ × ℝ)} (hR : MeasurableSet R)
    (hRfin : ((volume : Measure ℝ).prod ν) R < ⊤) :
    ∀ᵐ ω ∂μ, {k | ∃ n ∈ Finset.range (K k ω), X k n ω ∈ R}.Finite := by
  have hg1 : Measurable (R.indicator (fun _ : ℝ × ℝ => (1 : ℝ≥0∞))) :=
    measurable_const.indicator hR
  have hlintegral (g : ℝ × ℝ → ℝ≥0∞) (hg : Measurable g) (ω : Ω) :
      ∫⁻ x, g x ∂(poissonRandomMeasure K X ω)
        = ∑' k, ∑ n ∈ Finset.range (K k ω), g (X k n ω) := by
    rw [poissonRandomMeasure, lintegral_sum_measure]
    refine tsum_congr fun k => ?_
    rw [lintegral_sum_measure]
    have hterm : ∀ n, ∫⁻ x, g x ∂(if n < K k ω then Measure.dirac (X k n ω) else 0)
        = if n < K k ω then g (X k n ω) else 0 := fun n => by
      by_cases h : n < K k ω
      · rw [if_pos h, if_pos h, lintegral_dirac' _ hg]
      · rw [if_neg h, if_neg h, lintegral_zero_measure]
    simp_rw [hterm]
    rw [tsum_eq_sum (s := Finset.range (K k ω))
      fun n hn => if_neg (by simpa [Finset.mem_range] using hn)]
    exact Finset.sum_congr rfl fun n hn => if_pos (by simpa [Finset.mem_range] using hn)
  filter_upwards [ae_poissonRandomMeasure_apply_lt_top hd hR hRfin] with ω hω
  have hcount : ∑' k, ∑ n ∈ Finset.range (K k ω),
        R.indicator (fun _ : ℝ × ℝ => (1 : ℝ≥0∞)) (X k n ω)
      = poissonRandomMeasure K X ω R := by
    rw [← hlintegral _ hg1 ω, lintegral_indicator hR, setLIntegral_one]
  have hCfin : {k | (1 : ℝ≥0∞) ≤ ∑ n ∈ Finset.range (K k ω),
        R.indicator (fun _ : ℝ × ℝ => (1 : ℝ≥0∞)) (X k n ω)}.Finite :=
    ENNReal.finite_const_le_of_tsum_ne_top (by rw [hcount]; exact hω.ne) one_ne_zero
  refine hCfin.subset fun k hk => ?_
  simp only [Set.mem_setOf_eq] at hk ⊢
  obtain ⟨n, hn, hmem⟩ := hk
  calc (1 : ℝ≥0∞)
      = R.indicator (fun _ : ℝ × ℝ => (1 : ℝ≥0∞)) (X k n ω) := by
          rw [Set.indicator_of_mem hmem]
    _ ≤ _ := Finset.single_le_sum
        (f := fun n => R.indicator (fun _ : ℝ × ℝ => (1 : ℝ≥0∞)) (X k n ω))
        (fun _ _ => zero_le) hn
