-- Prove2me | solution 1 for ShockWear.WearProcess.proof410_grid
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T18:05:32.417822+00:00
-- url     : https://prove2.me/submissions/f3c14e0c-6738-409e-a92f-d7a819a267eb

import Mathlib
import Definitions.Def_ShockWear_WearProcess_Model
import Theorems.Thm_ShockWear_WearProcess_lemma41b
import Theorems.Thm_ShockWear_WearProcess_proof410_increments

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

open ShockWear.WearProcess

theorem solution {Ω : Type*} [MeasurableSpace Ω] (pr : Measure Ω)
    [IsProbabilityMeasure pr] (Z : ℝ≥0 → Ω → ℝ) (κ : ℝ≥0 → ℝ≥0 → Kernel ℝ ℝ)
    (hZ : IsWearProcess pr Z κ) (Δ : ℝ≥0) (hΔ : 0 < Δ) (x : ℝ) (j k : ℕ)
    (hj : 1 ≤ j) (hjk : j ≤ k) :
    wearCdf pr Z (k • Δ) x ^ (1 / ((k : ℝ) * (Δ : ℝ))) ≤
      wearCdf pr Z (j • Δ) x ^ (1 / ((j : ℝ) * (Δ : ℝ))) := by
  obtain ⟨κ', hκ'⟩ := proof410_increments pr Z κ hZ Δ hΔ
  have hL := lemma41b pr (wearIncr Z Δ) κ' hκ' x j k hj hjk
  -- telescoping: psum of increments is Z(nΔ) a.e.
  have hcdf : ∀ n : ℕ, (pr {ω | psum (wearIncr Z Δ) n ω ≤ x}).toReal = wearCdf pr Z (n • Δ) x := by
    intro n
    unfold wearCdf
    congr 1
    apply measure_congr
    filter_upwards [hZ.start_mono] with ω hω
    have hsum : psum (wearIncr Z Δ) n ω = Z (n • Δ) ω := by
      unfold psum wearIncr
      rw [Finset.sum_range_sub (fun i => Z (i • Δ) ω) n]
      simp [hω.1]
    show (psum (wearIncr Z Δ) n ω ≤ x) = (Z (n • Δ) ω ≤ x)
    rw [hsum]
  rw [hcdf, hcdf] at hL
  have hΔr : (0 : ℝ) ≤ 1 / (Δ : ℝ) := by positivity
  have h2 := Real.rpow_le_rpow (by unfold wearCdf; positivity) hL hΔr
  have hnn : ∀ n : ℕ, 0 ≤ wearCdf pr Z (n • Δ) x := fun n => by unfold wearCdf; positivity
  rw [← Real.rpow_mul (hnn k), ← Real.rpow_mul (hnn j)] at h2
  have e : ∀ n : ℕ, 1 / (n : ℝ) * (1 / (Δ : ℝ)) = 1 / ((n : ℝ) * (Δ : ℝ)) := fun n => by
    rw [one_div_mul_one_div]
  rw [e, e] at h2
  exact h2
