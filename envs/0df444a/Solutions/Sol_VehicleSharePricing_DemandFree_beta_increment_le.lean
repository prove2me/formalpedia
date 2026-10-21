-- Prove2me | solution 1 for VehicleSharePricing.DemandFree.beta_increment_le
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T20:41:44.796865+00:00
-- url     : https://prove2.me/submissions/c4446f51-9ec9-4c2c-a7f2-eb78fb93d4b0

import Mathlib
import Definitions.Def_VehicleSharePricing_DemandFree_Beta

set_option autoImplicit false
open VehicleSharePricing.DemandFree

lemma beta_succ_eq (N : ℕ) (Δ : ℝ) (K : ℕ) :
    beta N Δ (K + 1) = ((K : ℝ) + 1) / ((N : ℝ) + K + Δ * (1 - beta N Δ K)) := by
  rw [beta]; congr 1; ring

lemma beta_bounds (N : ℕ) (hN : 1 ≤ N) (Δ : ℝ) (hΔ : 0 < Δ) :
    ∀ K : ℕ, 0 ≤ beta N Δ K ∧ beta N Δ K ≤ 1 := by
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  intro K
  induction K with
  | zero => simp [beta]
  | succ K ih =>
    obtain ⟨h0, h1⟩ := ih
    have hK : (0 : ℝ) ≤ K := Nat.cast_nonneg K
    have hD : (0 : ℝ) < (N : ℝ) + K + Δ * (1 - beta N Δ K) := by nlinarith
    rw [beta_succ_eq]
    refine ⟨by positivity, ?_⟩
    rw [div_le_one hD]
    nlinarith

lemma beta_main (N : ℕ) (hN : 1 ≤ N) (Δ : ℝ) (hΔ : 0 < Δ) :
    ∀ K : ℕ, beta N Δ K ≤ (K : ℝ) / ((N : ℝ) + Δ) ∧
      beta N Δ (K + 1) ≤ beta N Δ K + 1 / ((N : ℝ) + Δ) := by
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hs : (0 : ℝ) < (N : ℝ) + Δ := by linarith
  have hδ : (1 / ((N : ℝ) + Δ)) * ((N : ℝ) + Δ) = 1 := by field_simp
  have hδ0 : (0 : ℝ) < 1 / ((N : ℝ) + Δ) := by positivity
  set δ : ℝ := 1 / ((N : ℝ) + Δ) with hδdef
  have hKδ : ∀ K : ℕ, (K : ℝ) / ((N : ℝ) + Δ) = K * δ := by
    intro K; rw [hδdef]; ring
  intro K
  induction K with
  | zero =>
    refine ⟨by simp [beta], ?_⟩
    rw [beta_succ_eq]
    simp [beta]
    rw [hδdef]
    apply le_of_eq
    congr 1
    ring
  | succ K ih =>
    obtain ⟨ihA, ihB⟩ := ih
    rw [hKδ] at ihA
    rw [hKδ]
    have hb := beta_bounds N hN Δ hΔ
    obtain ⟨hx0, hx1⟩ := hb K
    obtain ⟨hy0, hy1⟩ := hb (K + 1)
    have hK : (0 : ℝ) ≤ K := Nat.cast_nonneg K
    set x := beta N Δ K with hxdef
    set y := beta N Δ (K + 1) with hydef
    have hD : (0 : ℝ) < (N : ℝ) + K + Δ * (1 - x) := by nlinarith
    have hy : y * ((N : ℝ) + K + Δ * (1 - x)) = (K : ℝ) + 1 := by
      have e : y = ((K : ℝ) + 1) / ((N : ℝ) + K + Δ * (1 - x)) := beta_succ_eq N Δ K
      rw [e]; field_simp
    have hyK : y ≤ ((K : ℝ) + 1) * δ := by
      have : y ≤ x + δ := ihB
      push_cast
      nlinarith
    refine ⟨by push_cast; exact hyK, ?_⟩
    have hE : (0 : ℝ) < (N : ℝ) + ((K + 1 : ℕ) : ℝ) + Δ * (1 - y) := by push_cast; nlinarith
    rw [beta_succ_eq, div_le_iff₀ hE]
    push_cast
    -- key facts
    have h1 : 0 ≤ y * Δ * (x + δ - y) := by
      have : 0 ≤ x + δ - y := by linarith
      positivity
    have h2 : y * ((N : ℝ) + K + Δ * (1 - y)) ≥ (K : ℝ) + 1 - y * Δ * δ := by nlinarith
    have h3 : y * (Δ - N) ≤ (K : ℝ) + 1 := by
      have e : y * (Δ - N) * (δ * (N + Δ)) ≤ ((K : ℝ) + 1) * (δ * (N + Δ)) := by
        have : y * (Δ - N) ≤ ((K : ℝ) + 1) * δ * (Δ - N) ∨ Δ - N < 0 := by
          by_cases h : 0 ≤ Δ - N
          · left; exact mul_le_mul_of_nonneg_right hyK h
          · right; linarith
        rcases this with h | h
        · have h' : ((K : ℝ) + 1) * δ * (Δ - N) ≤ ((K : ℝ) + 1) * (δ * (N + Δ)) := by
            have : 0 ≤ ((K : ℝ) + 1) * δ * (2 * N) := by positivity
            nlinarith
          rw [hδ] at h' ⊢
          nlinarith
        · have : y * (Δ - N) ≤ 0 := by nlinarith
          rw [hδ]
          nlinarith
      rw [hδ] at e
      linarith
    have h4 : (y + δ) * ((N : ℝ) + K + 1 + Δ * (1 - y)) =
        y * ((N : ℝ) + K + Δ * (1 - y)) + y + δ * ((N : ℝ) + K + 1 + Δ * (1 - y)) := by ring
    have h5 : y + δ * ((N : ℝ) + K + 1 + Δ * (1 - y)) - y * Δ * δ ≥ 1 := by
      have : δ * (((N : ℝ) + K + 1 + Δ * (1 - y)) - y * Δ + y * (N + Δ) - (N + Δ)) =
          δ * (K + 1 - y * (Δ - N)) := by ring
      have e2 : y + δ * ((N : ℝ) + K + 1 + Δ * (1 - y)) - y * Δ * δ - 1 =
          δ * (K + 1 - y * (Δ - N)) := by
        have : y = y * (δ * (N + Δ)) := by rw [hδ]; ring
        nlinarith
      have : 0 ≤ δ * (K + 1 - y * (Δ - N)) := mul_nonneg hδ0.le (by linarith)
      linarith
    nlinarith

theorem solution (N : ℕ) (hN : 1 ≤ N) (Δ : ℝ) (hΔ : 0 < Δ) (K : ℕ) (hK : 1 ≤ K) :
    beta N Δ K - beta N Δ (K - 1) ≤ beta N Δ 1 ∧ beta N Δ 1 = 1 / ((N : ℝ) + Δ) := by
  have h1 : beta N Δ 1 = 1 / ((N : ℝ) + Δ) := by
    rw [beta_succ_eq]; simp [beta]
  refine ⟨?_, h1⟩
  obtain ⟨k, rfl⟩ : ∃ k, K = k + 1 := ⟨K - 1, by omega⟩
  have := (beta_main N hN Δ hΔ k).2
  simp only [Nat.add_sub_cancel]
  rw [h1]
  linarith

