-- Prove2me | solution 1 for YeIPA.LP.potential_gradient_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T13:01:15.391673+00:00
-- url     : https://prove2.me/submissions/801652cc-5c23-4ce8-81e0-feee8338c8f2

import Mathlib
import Definitions.Def_YeIPA_LP_PotentialReduction

open Matrix
open YeIPA.LP

theorem g69w_final_ineq (m s σ T k ρ : ℝ) (hm : 0 < m) (hs : s = m + σ) (hk : 0 ≤ k)
    (hσ : k * m ≤ σ) (hT0 : 0 ≤ T) (hT : k ^ 2 ≤ T * σ) (hρ : k + 1 ≤ ρ ^ 2) (hρ0 : 0 ≤ ρ) :
    3 / 4 ≤ 1 + m * T + m * (ρ ^ 2 - (k + 1) ^ 2) / s := by
  have hs0 : 0 < s := by nlinarith
  have h1 : m * (ρ ^ 2 - (k + 1) ^ 2) / s ≥ - (m * (k * (k + 1)) / s) := by
    have e : m * (ρ ^ 2 - (k + 1) ^ 2) / s = m * (ρ ^ 2 - (k + 1)) / s - m * (k * (k + 1)) / s := by
      ring
    have : 0 ≤ m * (ρ ^ 2 - (k + 1)) / s := div_nonneg (mul_nonneg hm.le (by linarith)) hs0.le
    linarith
  rcases eq_or_lt_of_le hk with hk0 | hkpos
  · subst hk0
    have : m * T ≥ 0 := by positivity
    have : 0 ≤ m * (ρ ^ 2 - (0 + 1) ^ 2) / s := div_nonneg (mul_nonneg hm.le (by linarith)) hs0.le
    linarith
  · have hσ0 : 0 < σ := by nlinarith
    -- need 1/4 + m T - m k (k+1)/s ≥ 0
    have hmT : m * T ≥ m * k ^ 2 / σ := by
      rw [ge_iff_le, div_le_iff₀ hσ0]; nlinarith
    have key : m * (k * (k + 1)) / s ≤ 1 / 4 + m * k ^ 2 / σ := by
      rw [div_le_iff₀ hs0, hs]
      have : m * k ^ 2 / σ * σ = m * k ^ 2 := by field_simp
      have e : (1 / 4 + m * k ^ 2 / σ) * (m + σ) = (m + σ) / 4 + m * k ^ 2 * m / σ + m * k ^ 2 := by
        field_simp; ring
      rw [e]
      -- multiply through by 4σ
      have hpos : 0 < 4 * σ := by positivity
      rw [← mul_le_mul_iff_left₀ hpos]
      have e2 : ((m + σ) / 4 + m * k ^ 2 * m / σ + m * k ^ 2) * (4 * σ)
          = (m + σ) * σ + 4 * m * k ^ 2 * m + 4 * m * k ^ 2 * σ := by
        field_simp
      rw [e2]
      nlinarith [sq_nonneg (σ - 2 * k * m), mul_pos hm hσ0]
    linarith

theorem g69w_sum_identity {n : ℕ} (v : Fin n → ℝ) (hv : ∀ j, 0 < v j) (c : ℝ) :
    ∑ j, ((1 - c * v j) / Real.sqrt (v j)) ^ 2 =
      ∑ j, 1 / v j - 2 * c * n + c ^ 2 * ∑ j, v j := by
  have : ∀ j, ((1 - c * v j) / Real.sqrt (v j)) ^ 2 = 1 / v j - 2 * c + c ^ 2 * v j := by
    intro j
    have := hv j
    rw [div_pow, Real.sq_sqrt this.le]; field_simp; ring
  simp only [this, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Finset.mul_sum]
  ring

theorem solution {n : ℕ} (hn : 0 < n) (v : Fin n → ℝ)
    (hv : ∀ j, 0 < v j) (ρ : ℝ) (hρ : Real.sqrt n ≤ ρ) :
    Real.sqrt (3 / 4) ≤
      Real.sqrt (vmin v) *
        norm2 (fun j => (1 - ((n : ℝ) + ρ) / (∑ i, v i) * v j) / Real.sqrt (v j)) := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨j0, hj0⟩ := exists_eq_ciInf_of_finite (f := v)
  have hvmin : vmin v = v j0 := hj0.symm
  set m := v j0 with hmdef
  have hm : 0 < m := hv j0
  have hle : ∀ j, m ≤ v j := fun j => by rw [← hvmin]; exact ciInf_le (Finite.bddBelow_range _) j
  unfold norm2
  rw [hvmin, ← Real.sqrt_mul hm.le]
  apply Real.sqrt_le_sqrt
  set s := ∑ i, v i with hsdef
  rw [g69w_sum_identity v hv]
  set E := (Finset.univ : Finset (Fin n)).erase j0
  set σ := ∑ j ∈ E, v j
  set T := ∑ j ∈ E, 1 / v j
  have hsσ : s = m + σ := (Finset.add_sum_erase _ _ (Finset.mem_univ j0)).symm
  have hTσ : ∑ j, 1 / v j = 1 / m + T := (Finset.add_sum_erase _ _ (Finset.mem_univ j0)).symm
  have hcard : (E.card : ℝ) = (n : ℝ) - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin,
      Nat.cast_sub (by omega)]; simp
  have hσ : ((n : ℝ) - 1) * m ≤ σ := by
    rw [← hcard, ← nsmul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_le_sum fun j _ => hle j
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun j _ => (one_div_pos.mpr (hv j)).le
  have hT : ((n : ℝ) - 1) ^ 2 ≤ T * σ := by
    rcases (Finset.sum_nonneg (fun j (_ : j ∈ E) => (hv j).le)).eq_or_lt with h0 | hpos
    · have hσ0 : σ = 0 := h0.symm
      rw [hσ0, mul_zero]
      have : E = ∅ := by
        by_contra hne
        obtain ⟨j, hj⟩ := Finset.nonempty_iff_ne_empty.mpr hne
        have := Finset.sum_pos (fun j (_ : j ∈ E) => hv j) ⟨j, hj⟩
        linarith
      rw [this] at hcard; simp at hcard; nlinarith
    · have h := Finset.sq_sum_div_le_sum_sq_div E (fun _ => (1 : ℝ)) (g := v) (fun j _ => hv j)
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one, one_pow] at h
      rw [hcard, div_le_iff₀ hpos] at h
      exact h
  have hρ0 : 0 ≤ ρ := le_trans (Real.sqrt_nonneg _) hρ
  have hρ2 : ((n : ℝ) - 1) + 1 ≤ ρ ^ 2 := by
    have := Real.sq_sqrt (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    nlinarith [Real.sqrt_nonneg (n : ℝ)]
  have hk : (0 : ℝ) ≤ (n : ℝ) - 1 := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have key := g69w_final_ineq m s σ T ((n : ℝ) - 1) ρ hm hsσ hk hσ hT0 hT hρ2 hρ0
  have hs0 : 0 < s := by rw [hsσ]; nlinarith
  rw [hTσ]
  have e : m * (1 / m + T - 2 * (((n : ℝ) + ρ) / s) * n + (((n : ℝ) + ρ) / s) ^ 2 * s)
      = 1 + m * T + m * (ρ ^ 2 - ((n : ℝ) - 1 + 1) ^ 2) / s := by
    field_simp; ring
  rw [e]; exact key
