-- Prove2me | solution 1 for ShockWear.WearProcess.proof410_all_times
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T18:07:39.619028+00:00
-- url     : https://prove2.me/submissions/f2da5749-66dd-4a34-996f-f79c1f0d85aa

import Mathlib
import Definitions.Def_ShockWear_WearProcess_Model
import Theorems.Thm_ShockWear_WearProcess_proof410_grid

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

open ShockWear.WearProcess

theorem solution {Ω : Type*} [MeasurableSpace Ω] (pr : Measure Ω)
    [IsProbabilityMeasure pr] (Z : ℝ≥0 → Ω → ℝ) (κ : ℝ≥0 → ℝ≥0 → Kernel ℝ ℝ)
    (hZ : IsWearProcess pr Z κ) (x : ℝ) (s t : ℝ≥0) (hs : 0 < s) (hst : s ≤ t) :
    wearCdf pr Z t x ^ (1 / (t : ℝ)) ≤ wearCdf pr Z s x ^ (1 / (s : ℝ)) := by
  have hnn : ∀ a, 0 ≤ wearCdf pr Z a x := fun a => by unfold wearCdf; positivity
  have hanti : ∀ a b : ℝ≥0, a ≤ b → wearCdf pr Z b x ≤ wearCdf pr Z a x := by
    intro a b hab
    unfold wearCdf
    apply ENNReal.toReal_mono (measure_ne_top _ _)
    apply measure_mono_ae
    filter_upwards [hZ.start_mono] with ω hω h
    exact le_trans (hω.2 hab) h
  have hsR : (0 : ℝ) < s := hs
  have htR : (0 : ℝ) < t := lt_of_lt_of_le hs hst
  have hstR : (s : ℝ) ≤ t := hst
  set c := wearCdf pr Z s x ^ (1 / (s : ℝ)) with hc
  have hc0 : 0 ≤ c := Real.rpow_nonneg (hnn s) _
  -- grid data
  let Δ : ℕ → ℝ≥0 := fun n => s / ((n : ℝ≥0) + 1)
  have hΔR : ∀ n, ((Δ n : ℝ≥0) : ℝ) = (s : ℝ) / ((n : ℝ) + 1) := fun n => by
    simp [Δ]
  have hΔpos : ∀ n, 0 < Δ n := fun n => by
    simp only [Δ]; positivity
  have hΔposR : ∀ n, (0 : ℝ) < Δ n := fun n => hΔpos n
  let K : ℕ → ℕ := fun n => ⌊(t : ℝ) / (Δ n : ℝ)⌋₊
  have hjK : ∀ n, n + 1 ≤ K n := by
    intro n
    apply Nat.le_floor
    rw [hΔR, div_div_eq_mul_div, le_div_iff₀ hsR]
    push_cast
    nlinarith [hstR, (by positivity : (0:ℝ) ≤ (n:ℝ) + 1)]
  have hKΔ : ∀ n, ((K n : ℝ) * (Δ n : ℝ)) ≤ t := by
    intro n
    have := Nat.floor_le (a := (t : ℝ) / (Δ n : ℝ)) (by positivity)
    calc (K n : ℝ) * (Δ n : ℝ) ≤ (t : ℝ) / (Δ n : ℝ) * (Δ n : ℝ) :=
          mul_le_mul_of_nonneg_right this (hΔposR n).le
      _ = t := div_mul_cancel₀ _ (hΔposR n).ne'
  have hKΔlow : ∀ n, (t : ℝ) - (Δ n : ℝ) ≤ (K n : ℝ) * (Δ n : ℝ) := by
    intro n
    have := Nat.lt_floor_add_one ((t : ℝ) / (Δ n : ℝ))
    have h2 : (t : ℝ) / (Δ n : ℝ) * (Δ n : ℝ) = t := div_mul_cancel₀ _ (hΔposR n).ne'
    nlinarith [hΔposR n]
  have hjΔ : ∀ n, (n + 1) • Δ n = s := by
    intro n
    simp only [Δ, nsmul_eq_mul]
    push_cast
    field_simp
  have hcoe : ∀ (m : ℕ) (a : ℝ≥0), (((m • a : ℝ≥0)) : ℝ) = (m : ℝ) * (a : ℝ) := fun m a => by
    simp [nsmul_eq_mul]
  -- main bound
  let r : ℕ → ℝ := fun n => (K n : ℝ) * (Δ n : ℝ) / t
  have hbound : ∀ n, wearCdf pr Z t x ^ (1 / (t : ℝ)) ≤ c ^ r n := by
    intro n
    have hKpos : (0 : ℝ) < (K n : ℝ) * (Δ n : ℝ) := by
      have : (1 : ℝ) ≤ K n := by exact_mod_cast le_trans (by omega) (hjK n)
      nlinarith [hΔposR n]
    have hle : K n • Δ n ≤ t := by
      rw [← NNReal.coe_le_coe, hcoe]; exact hKΔ n
    have hg := proof410_grid pr Z κ hZ (Δ n) (hΔpos n) x (n + 1) (K n) (by omega) (hjK n)
    rw [hjΔ] at hg
    have hjs : ((n + 1 : ℕ) : ℝ) * (Δ n : ℝ) = s := by
      rw [← hcoe, hjΔ]
    rw [hjs] at hg
    set a := wearCdf pr Z (K n • Δ n) x
    have h1 : wearCdf pr Z t x ^ (1 / (t : ℝ)) ≤ a ^ (1 / (t : ℝ)) :=
      Real.rpow_le_rpow (hnn t) (hanti _ _ hle) (by positivity)
    have h2 : a ^ (1 / (t : ℝ)) = (a ^ (1 / ((K n : ℝ) * (Δ n : ℝ)))) ^ r n := by
      rw [← Real.rpow_mul (hnn _)]
      congr 1
      simp only [r]
      field_simp
      exact (div_self hKpos.ne').symm
    have h3 : (a ^ (1 / ((K n : ℝ) * (Δ n : ℝ)))) ^ r n ≤ c ^ r n :=
      Real.rpow_le_rpow (Real.rpow_nonneg (hnn _) _) hg (by simp only [r]; positivity)
    linarith
  -- r n → 1
  have hr : Tendsto r atTop (𝓝 1) := by
    have hlow : Tendsto (fun n : ℕ => 1 - (s : ℝ) / t * (1 / ((n : ℝ) + 1))) atTop (𝓝 1) := by
      have := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
      have := (this.const_mul ((s : ℝ) / t)).const_sub 1
      simpa using this
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds
    · intro n
      simp only [r]
      rw [le_div_iff₀ htR]
      have := hKΔlow n
      rw [hΔR] at this ⊢
      have e : (1 - (s : ℝ) / t * (1 / ((n : ℝ) + 1))) * t = t - s / ((n : ℝ) + 1) := by
        field_simp
      linarith
    · intro n
      simp only [r]
      rw [div_le_one htR]
      exact hKΔ n
  have hlim : Tendsto (fun n => c ^ r n) atTop (𝓝 (c ^ (1 : ℝ))) :=
    tendsto_const_nhds.rpow hr (Or.inr one_pos)
  rw [Real.rpow_one] at hlim
  exact ge_of_tendsto' hlim hbound
