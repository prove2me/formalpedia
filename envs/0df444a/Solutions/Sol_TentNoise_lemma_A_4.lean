-- Prove2me | solution 1 for TentNoise.lemma_A_4
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-18T05:47:12.652005+00:00
-- url     : https://prove2.me/submissions/72074ad1-3965-4d79-bf04-14306145ec41

import Mathlib

open Set Real MeasureTheory

theorem solution (α : ℝ) (hα : 0 < α) :
    (Summable (fun n : ℕ => Real.exp (-α * ((n : ℝ) + 1) ^ 2)) ∧
      ∑' n : ℕ, Real.exp (-α * ((n : ℝ) + 1) ^ 2) ≤ Real.sqrt Real.pi / (2 * Real.sqrt α)) ∧
    (Summable (fun n : ℕ => ((n : ℝ) + 1) * Real.exp (-α * ((n : ℝ) + 1) ^ 2)) ∧
      ∑' n : ℕ, ((n : ℝ) + 1) * Real.exp (-α * ((n : ℝ) + 1) ^ 2) ≤ 1 / α) := by
  constructor
  · set f : ℝ → ℝ := fun x => Real.exp (-α * x ^ 2) with hf
    have hval : Real.sqrt Real.pi / (2 * Real.sqrt α) = ∫ x in Ioi (0:ℝ), f x := by
      rw [hf, integral_gaussian_Ioi, Real.sqrt_div' _ hα.le]; ring
    have hpart : ∀ N : ℕ, ∑ n ∈ Finset.range N, Real.exp (-α * ((n : ℝ) + 1) ^ 2) ≤
        Real.sqrt Real.pi / (2 * Real.sqrt α) := by
      intro N
      have hanti : AntitoneOn f (Icc 0 (0 + (N:ℝ))) := by
        intro x hx y hy hxy
        simp only [hf]
        apply Real.exp_le_exp.mpr
        have : x ^ 2 ≤ y ^ 2 := by nlinarith [hx.1, hy.1]
        nlinarith
      have h1 := hanti.sum_le_integral
      simp only [zero_add, Nat.cast_add, Nat.cast_one] at h1
      calc ∑ n ∈ Finset.range N, Real.exp (-α * ((n : ℝ) + 1) ^ 2)
          ≤ ∫ x in (0:ℝ)..N, f x := h1
        _ = ∫ x in Ioc (0:ℝ) N, f x := intervalIntegral.integral_of_le (by positivity)
        _ ≤ ∫ x in Ioi (0:ℝ), f x := by
            apply setIntegral_mono_set
            · exact (integrable_exp_neg_mul_sq hα).integrableOn
            · exact Filter.Eventually.of_forall (fun x => (Real.exp_pos _).le)
            · exact Filter.Eventually.of_forall Ioc_subset_Ioi_self
        _ = _ := hval.symm
    have hs := summable_of_sum_range_le (fun n => (Real.exp_pos _).le) hpart
    exact ⟨hs, hs.tsum_le_of_sum_range_le hpart⟩
  · set g : ℕ → ℝ := fun n => Real.exp (-α * (n : ℝ) ^ 2) with hg
    have hterm : ∀ n : ℕ, ((n : ℝ) + 1) * Real.exp (-α * ((n : ℝ) + 1) ^ 2) ≤
        (g n - g (n + 1)) / α := by
      intro n
      simp only [hg, Nat.cast_add, Nat.cast_one]
      rw [le_div_iff₀ hα]
      have hy : α * ((n:ℝ) + 1) + 1 ≤ Real.exp (α * (2 * (n:ℝ) + 1)) := by
        have := Real.add_one_le_exp (α * (2 * (n:ℝ) + 1))
        have : 0 ≤ α * (n:ℝ) := by positivity
        nlinarith
      have hsplit : Real.exp (-α * (n:ℝ) ^ 2) =
          Real.exp (α * (2 * (n:ℝ) + 1)) * Real.exp (-α * ((n:ℝ) + 1) ^ 2) := by
        rw [← Real.exp_add]; congr 1; ring
      rw [hsplit]
      have he := Real.exp_pos (-α * ((n:ℝ) + 1) ^ 2)
      nlinarith
    have hpart : ∀ N : ℕ, ∑ n ∈ Finset.range N, ((n : ℝ) + 1) * Real.exp (-α * ((n : ℝ) + 1) ^ 2)
        ≤ 1 / α := by
      intro N
      calc _ ≤ ∑ n ∈ Finset.range N, (g n - g (n + 1)) / α := Finset.sum_le_sum (fun n _ => hterm n)
        _ = (g 0 - g N) / α := by rw [← Finset.sum_div, Finset.sum_range_sub']
        _ ≤ 1 / α := by
            apply div_le_div_of_nonneg_right _ hα.le
            simp only [hg, Nat.cast_zero]
            have := Real.exp_pos (-(α * (N:ℝ) ^ 2))
            norm_num; linarith
    have hs := summable_of_sum_range_le (fun n => by positivity) hpart
    exact ⟨hs, hs.tsum_le_of_sum_range_le hpart⟩
