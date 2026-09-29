-- Prove2me | solution 1 for RobustSDP.Unstructured.theorem_5_2
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T23:23:49.223528+00:00
-- url     : https://prove2.me/submissions/2a5e38f3-c2be-45ef-ac0f-528f29a12eb8

import Mathlib
import Definitions.Def_RobustSDP_Unstructured_Model

open Matrix
open scoped Matrix.Norms.L2Operator

namespace RobustSDP.Unstructured

lemma aux_t52_sum_expand {m : ℕ} (u x : Fin m → ℝ) (c : ℝ) :
    ∑ j, (u j + c * x j) ^ 2 = ∑ j, u j ^ 2 + 2 * c * ∑ j, u j * x j + c ^ 2 * ∑ j, x j ^ 2 := by
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

lemma aux_t52_amgm {m : ℕ} (u x : Fin m → ℝ) (c : ℝ) :
    -(2 * c * ∑ j, u j * x j) ≤ ∑ j, u j ^ 2 + c ^ 2 * ∑ j, x j ^ 2 := by
  have h : 0 ≤ ∑ j, (u j + c * x j) ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  rw [aux_t52_sum_expand] at h
  linarith

end RobustSDP.Unstructured

open RobustSDP.Unstructured
open Matrix
open scoped Matrix.Norms.L2Operator

theorem solution {m K : ℕ} (a : Fin K → Fin m → ℝ) (b : Fin K → ℝ) (ρ : ℝ) (hρ : 0 < ρ)
    (x : Fin m → ℝ) :
    (∀ i : Fin K, ∀ δa : Fin m → ℝ, ∀ δb : ℝ, ∑ j, δa j ^ 2 + δb ^ 2 ≤ ρ ^ 2 →
        (a i + δa) ⬝ᵥ x ≥ b i + δb) ↔
      ∀ i : Fin K, a i ⬝ᵥ x - ρ * Real.sqrt (∑ j, x j ^ 2 + 1) ≥ b i := by
  set B : ℝ := ∑ j, x j ^ 2 with hB
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun j _ => sq_nonneg _
  set s : ℝ := Real.sqrt (B + 1) with hs
  have hs0 : 0 < s := Real.sqrt_pos.mpr (by linarith)
  have hs2 : s ^ 2 = B + 1 := Real.sq_sqrt (by linarith)
  have hdot : ∀ (u : Fin m → ℝ), u ⬝ᵥ x = ∑ j, u j * x j := fun u => rfl
  constructor
  · intro h i
    set c : ℝ := ρ / s with hc
    have hcs : c * s = ρ := by rw [hc]; field_simp
    have key := h i (fun j => -c * x j) c (by
      have : ∑ j, (-c * x j) ^ 2 = c ^ 2 * B := by
        rw [hB, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        ring
      rw [this]
      have : c ^ 2 * B + c ^ 2 = (c * s) ^ 2 := by rw [mul_pow, hs2]; ring
      rw [this, hcs])
    rw [add_dotProduct] at key
    have h2 : (fun j => -c * x j) ⬝ᵥ x = -c * B := by
      rw [hdot, hB, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [h2] at key
    have : ρ * s = c * (B + 1) := by rw [← hs2, ← hcs]; ring
    rw [this]
    linarith
  · intro h i δa δb hδ
    have hi := h i
    rw [add_dotProduct]
    set A : ℝ := ∑ j, δa j ^ 2 with hA
    set p : ℝ := δa ⬝ᵥ x with hp
    set c : ℝ := ρ / s with hc
    have hc0 : 0 < c := div_pos hρ hs0
    have hcs : c * s = ρ := by rw [hc]; field_simp
    have h1 : -(2 * c * p) ≤ A + c ^ 2 * B := by
      rw [hp, hdot, hA, hB]; exact aux_t52_amgm δa x c
    have h2 : 2 * c * δb ≤ δb ^ 2 + c ^ 2 := by nlinarith [sq_nonneg (δb - c)]
    -- 2c(δb - p) ≤ A + δb^2 + c^2 (B+1) ≤ ρ^2 + ρ^2
    have h3 : c ^ 2 * (B + 1) = ρ ^ 2 := by rw [← hs2, ← hcs]; ring
    have h4 : c * (δb - p) ≤ ρ ^ 2 := by nlinarith
    have h5 : ρ ^ 2 = c * (ρ * s) := by rw [← hcs]; ring
    rw [h5] at h4
    have h6 : δb - p ≤ ρ * s := le_of_mul_le_mul_left h4 hc0
    linarith
