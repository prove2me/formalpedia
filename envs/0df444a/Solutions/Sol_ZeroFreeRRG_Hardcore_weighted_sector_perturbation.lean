-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.weighted_sector_perturbation
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T09:28:58.656279+00:00
-- url     : https://prove2.me/submissions/e6449f97-6df8-4c26-9f5a-52b86c15718c

import Mathlib
set_option autoImplicit false
open scoped Classical BigOperators

theorem solution {ι : Type} (S : Finset ι) (z a b : ι → ℂ) (δ τ : ℝ)
    (hδ : 0 ≤ δ) (hδ1 : δ < 1) (hτ : 0 < τ)
    (ha : ∀ i ∈ S, 1-δ ≤ ‖a i‖)
    (hab : ∀ i ∈ S, ‖b i-a i‖ ≤ δ)
    (hsector : τ*(∑ i ∈ S, ‖z i‖) ≤ ‖∑ i ∈ S, z i‖) :
    ‖(∑ i ∈ S, (b i/a i)*z i) - ∑ i ∈ S, z i‖ ≤
      (δ/(τ*(1-δ))) * ‖∑ i ∈ S, z i‖ := by
  classical
  have hden : 0 < 1-δ := by linarith
  have hr0 : 0 ≤ δ/(1-δ) := div_nonneg hδ hden.le
  have hr (i : ι) (hi : i ∈ S) : ‖b i/a i-1‖ ≤ δ/(1-δ) := by
    have hap : 0 < ‖a i‖ := lt_of_lt_of_le hden (ha i hi)
    have hane : a i ≠ 0 := norm_pos_iff.mp hap
    rw [div_sub_one hane,norm_div]
    calc
      _ ≤ δ/‖a i‖ := div_le_div_of_nonneg_right (hab i hi) (norm_nonneg _)
      _ ≤ δ/(1-δ) := div_le_div_of_nonneg_left hδ hden (ha i hi)
  have hpt (i : ι) (hi : i ∈ S) : ‖(b i/a i-1)*z i‖ ≤ (δ/(1-δ))*‖z i‖ := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hr i hi) (norm_nonneg _)
  have hbound : (∑ i ∈ S, ‖z i‖) ≤ ‖∑ i ∈ S, z i‖/τ := by
    apply (le_div_iff₀ hτ).2
    nlinarith [hsector]
  calc
    _ = ‖∑ i ∈ S, (b i/a i-1)*z i‖ := by
      congr 1
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ ≤ ∑ i ∈ S, ‖(b i/a i-1)*z i‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ S, (δ/(1-δ))*‖z i‖ := Finset.sum_le_sum hpt
    _ = (δ/(1-δ))*(∑ i ∈ S, ‖z i‖) := by rw [Finset.mul_sum]
    _ ≤ (δ/(1-δ))*(‖∑ i ∈ S, z i‖/τ) := mul_le_mul_of_nonneg_left hbound hr0
    _ = _ := by
      field_simp <;> ring
