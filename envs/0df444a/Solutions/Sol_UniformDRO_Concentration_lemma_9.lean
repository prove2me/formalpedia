-- Prove2me | solution 1 for UniformDRO.Concentration.lemma_9
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-19T15:39:59.553483+00:00
-- url     : https://prove2.me/submissions/aa5f9c72-f365-4550-9c60-55a5ebce252c

import Mathlib
import Definitions.Def_UniformDRO_Concentration_RobustRisk

open MeasureTheory UniformDRO.Concentration

theorem solution {X : Type*} [MeasurableSpace X] (P : Measure X) [IsProbabilityMeasure P]
    (k ρ : ℝ) (hk : 1 < k) (hρ : 0 < ρ) (Z : X → ℝ) (hZm : Measurable Z) (M : ℝ)
    (hZ : ∀ x, Z x ∈ Set.Icc 0 M) :
    ⨅ η : ℝ, dualObjective k ρ P Z η =
      ⨅ η : Set.Icc (-(M / (ck k ρ - 1))) M, dualObjective k ρ P Z η := by
  set q := kstar k with hq
  have hq1 : 1 < q := by rw [hq]; unfold kstar; rw [lt_div_iff₀ (by linarith)]; linarith
  have hq0 : 0 < q := by linarith
  set c := ck k ρ with hcdef
  have hc1 : 1 < c := by
    rw [hcdef]; unfold ck
    have : 1 < 1 + k * (k - 1) * ρ := by
      have : 0 < k * (k - 1) * ρ := mul_pos (mul_pos (by linarith) (by linarith)) hρ
      linarith
    exact Real.one_lt_rpow this (div_pos one_pos (by linarith))
  obtain ⟨x0⟩ : Nonempty X := by
    rcases isEmpty_or_nonempty X with h | h
    · exfalso
      have h1 := measure_univ (μ := P)
      rw [Set.univ_eq_empty_iff.mpr h, measure_empty] at h1
      exact zero_ne_one h1
    · exact h
  have hM0 : 0 ≤ M := (hZ x0).1.trans (hZ x0).2
  set a := -(M / (c - 1)) with ha
  have ha0 : a ≤ 0 := by rw [ha]; have := div_nonneg hM0 (by linarith : (0:ℝ) ≤ c - 1); linarith
  set g := dualObjective k ρ P Z with hg
  -- integrand facts
  have hint : ∀ η : ℝ, 0 ≤ ∫ x, (max (Z x - η) 0) ^ q ∂P :=
    fun η => integral_nonneg (fun x => Real.rpow_nonneg (le_max_right _ _) _)
  have hg_ge : ∀ η, η ≤ g η := by
    intro η; simp only [hg, dualObjective]
    have : 0 ≤ c * (∫ x, (max (Z x - η) 0) ^ q ∂P) ^ (1 / q) :=
      mul_nonneg (by linarith) (Real.rpow_nonneg (hint η) _)
    rw [← hq]; linarith
  have hg_big : ∀ η, M ≤ η → g η = η := by
    intro η hη; simp only [hg, dualObjective]
    have : ∀ x, max (Z x - η) 0 = 0 := fun x => max_eq_right (by linarith [(hZ x).2])
    simp only [this, Real.zero_rpow hq0.ne', integral_zero, ← hq]
    rw [Real.zero_rpow (by positivity)]; ring
  have hg_small : ∀ η, η ≤ a → M ≤ g η := by
    intro η hη
    have hη0 : η ≤ 0 := hη.trans ha0
    have hpt : ∀ x, (-η) ^ q ≤ (max (Z x - η) 0) ^ q := fun x =>
      Real.rpow_le_rpow (by linarith) (le_max_of_le_left (by linarith [(hZ x).1])) hq0.le
    have hbdd : Integrable (fun x => (max (Z x - η) 0) ^ q) P := by
      refine Integrable.of_bound (C := (M - η) ^ q) ?_ (Filter.Eventually.of_forall fun x => ?_)
      · exact (((hZm.sub_const η).max measurable_const).pow_const q).aestronglyMeasurable
      · rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (le_max_right _ _) _)]
        exact Real.rpow_le_rpow (le_max_right _ _) (max_le (by linarith [(hZ x).2]) (by linarith)) hq0.le
    have hI : (-η) ^ q ≤ ∫ x, (max (Z x - η) 0) ^ q ∂P := by
      have := integral_mono (integrable_const _) hbdd hpt
      simpa using this
    have hroot : -η ≤ (∫ x, (max (Z x - η) 0) ^ q ∂P) ^ (1 / q) := by
      have := Real.rpow_le_rpow (Real.rpow_nonneg (by linarith) _) hI (by positivity : (0:ℝ) ≤ 1 / q)
      rwa [← Real.rpow_mul (by linarith), mul_one_div_cancel hq0.ne', Real.rpow_one] at this
    simp only [hg, dualObjective, ← hq]
    have hmul : c * (-η) ≤ c * (∫ x, (max (Z x - η) 0) ^ q ∂P) ^ (1 / q) :=
      mul_le_mul_of_nonneg_left hroot (by linarith)
    -- (c - 1)(-η) ≥ M
    have hcη : M ≤ (c - 1) * (-η) := by
      have : M / (c - 1) ≤ -η := by rw [ha] at hη; linarith
      rw [div_le_iff₀ (by linarith)] at this; linarith
    nlinarith
  -- bounded below
  have hbelow : BddBelow (Set.range g) := ⟨min a M, by
    rintro _ ⟨η, rfl⟩
    rcases le_or_gt η a with h | h
    · exact (min_le_right _ _).trans (hg_small η h)
    · exact (min_le_left _ _).trans (h.le.trans (hg_ge η))⟩
  have hbelowI : BddBelow (Set.range fun η : Set.Icc a M => g η) :=
    ⟨min a M, by rintro _ ⟨η, rfl⟩; exact (min_le_left _ _).trans (η.2.1.trans (hg_ge η))⟩
  have hgM : g M = M := hg_big M le_rfl
  have hMI : M ∈ Set.Icc a M := ⟨by linarith, le_rfl⟩
  haveI : Nonempty (Set.Icc a M) := ⟨⟨M, hMI⟩⟩
  apply le_antisymm
  · exact le_ciInf (fun η => ciInf_le hbelow η.1)
  · refine le_ciInf (fun η => ?_)
    by_cases hin : η ∈ Set.Icc a M
    · exact ciInf_le hbelowI ⟨η, hin⟩
    · have hle : (⨅ η : Set.Icc a M, g η) ≤ M := by
        have := ciInf_le hbelowI ⟨M, hMI⟩; rwa [hgM] at this
      rcases not_and_or.mp hin with h | h
      · exact hle.trans (hg_small η (le_of_lt (not_le.mp h)))
      · rw [hg_big η (le_of_lt (not_le.mp h))]; linarith [not_le.mp h]
