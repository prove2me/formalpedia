-- Prove2me | solution 1 for PoWMining.CostStatics.eq_B2_ci
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T19:14:22.162993+00:00
-- url     : https://prove2.me/submissions/54d12524-e33c-40ef-b264-f272c2b03cdb

import Mathlib
import Definitions.Def_PoWMining_CostStatics_Setting

open PoWMining.CostStatics

lemma pow_cumCost_update {n : ℕ} (c : Fin n → ℝ) (k : Fin n) (t : ℝ) :
    cumCost (Function.update c k t) = t + (cumCost c - c k) := by
  unfold cumCost
  rw [Finset.sum_update_of_mem (Finset.mem_univ k)]
  have h := Finset.sum_eq_add_sum_sdiff_singleton_of_mem (Finset.mem_univ k) c
  linarith

lemma pow_cumCost_pos {n : ℕ} (c : Fin n → ℝ) (γ R : ℝ) (hS : Standing c γ R) :
    0 < cumCost c := by
  have hn : 0 < n := by have := hS.two_le; omega
  unfold cumCost
  exact Finset.sum_pos (fun k _ => hS.c_pos k) ⟨⟨0, hn⟩, Finset.mem_univ _⟩

lemma pow_g_pos {n : ℕ} (c : Fin n → ℝ) (γ R : ℝ) (hS : Standing c γ R) :
    0 < gH c γ R := by
  have hC := pow_cumCost_pos c γ R hS
  have hn : (2 : ℝ) ≤ n := by exact_mod_cast hS.two_le
  have hR := hS.R_pos
  unfold gH
  split_ifs with hγ
  · apply div_pos _ (by linarith)
    rw [sub_pos, Real.lt_sqrt hC.le]
    nlinarith [mul_pos (mul_pos hR hγ) (show (0:ℝ) < n - 1 by linarith)]
  · exact div_pos (mul_pos (by linarith) hR) hC

lemma pow_sqrt_eq {n : ℕ} (c : Fin n → ℝ) (γ R : ℝ) (hγ : 0 < γ) :
    Real.sqrt (cumCost c ^ 2 + 4 * ((n : ℝ) - 1) * R * γ) = cumCost c + 2 * γ * gH c γ R := by
  unfold gH
  rw [if_pos hγ]
  field_simp
  ring

lemma pow_K_pos {n : ℕ} (c : Fin n → ℝ) (γ R : ℝ) (hS : Standing c γ R) :
    0 < cumCost c + 2 * γ * gH c γ R := by
  have := pow_cumCost_pos c γ R hS
  have := pow_g_pos c γ R hS
  have := hS.γ_nonneg
  positivity

lemma pow_hasDerivAt_g {n : ℕ} (c : Fin n → ℝ) (γ R : ℝ) (hS : Standing c γ R) (k : Fin n) :
    HasDerivAt (fun t => gH (Function.update c k t) γ R)
      (-(gH c γ R) / (cumCost c + 2 * γ * gH c γ R)) (c k) := by
  have hC := pow_cumCost_pos c γ R hS
  have hg := pow_g_pos c γ R hS
  have hK := pow_K_pos c γ R hS
  have hn : (2 : ℝ) ≤ n := by exact_mod_cast hS.two_le
  have hR := hS.R_pos
  set A := cumCost c - c k with hA
  have hCA : c k + A = cumCost c := by rw [hA]; ring
  have hupd : ∀ t, cumCost (Function.update c k t) = t + A := fun t => by
    rw [pow_cumCost_update]
  by_cases hγ : 0 < γ
  · have hfun : (fun t => gH (Function.update c k t) γ R) =
        fun t => (Real.sqrt ((t + A) ^ 2 + 4 * ((n : ℝ) - 1) * R * γ) - (t + A)) / (2 * γ) := by
      funext t
      unfold gH
      rw [if_pos hγ, hupd]
    rw [hfun]
    have hD : (c k + A) ^ 2 + 4 * ((n : ℝ) - 1) * R * γ ≠ 0 := by
      rw [hCA]
      have : 0 < (n : ℝ) - 1 := by linarith
      have : 0 < ((n : ℝ) - 1) * R * γ := by positivity
      nlinarith
    have h1 : HasDerivAt (fun t => (t + A) ^ 2 + 4 * ((n : ℝ) - 1) * R * γ)
        (2 * (c k + A)) (c k) := by
      have := ((hasDerivAt_id (c k)).add_const A).pow 2
      simpa using this.add_const (4 * ((n : ℝ) - 1) * R * γ)
    have h2 := (h1.sqrt hD).sub ((hasDerivAt_id (c k)).add_const A)
    have h3 := h2.div_const (2 * γ)
    refine h3.congr_deriv ?_
    rw [hCA, pow_sqrt_eq c γ R hγ]
    field_simp
    ring
  · have hγ0 : γ = 0 := le_antisymm (not_lt.mp hγ) hS.γ_nonneg
    have hfun : (fun t => gH (Function.update c k t) γ R) =
        fun t => ((n : ℝ) - 1) * R * (t + A)⁻¹ := by
      funext t
      unfold gH
      rw [if_neg hγ, hupd, div_eq_mul_inv]
    rw [hfun]
    have h1 := ((hasDerivAt_id (c k)).add_const A).inv (by rw [id, hCA]; exact hC.ne')
    have h2 := h1.const_mul (((n : ℝ) - 1) * R)
    refine h2.congr_deriv ?_
    unfold gH
    rw [if_neg hγ]
    simp only [id, hCA, hγ0]
    field_simp
    ring

theorem solution {n : ℕ} (c : Fin n → ℝ) (γ R : ℝ) (hS : Standing c γ R) (i : Fin n) :
    HasDerivAt (fun t => gH (Function.update c i t) γ R)
      (-(gH c γ R) / (cumCost c + 2 * γ * gH c γ R)) (c i) ∧
    -(gH c γ R) / (cumCost c + 2 * γ * gH c γ R) < 0 ∧
    (0 < γ → 1 / (2 * γ) * (cumCost c / Real.sqrt (cumCost c ^ 2 + 4 * ((n : ℝ) - 1) * R * γ) - 1)
      = -(gH c γ R) / (cumCost c + 2 * γ * gH c γ R)) := by
  refine ⟨pow_hasDerivAt_g c γ R hS i, ?_, ?_⟩
  · exact div_neg_of_neg_of_pos (neg_neg_of_pos (pow_g_pos c γ R hS)) (pow_K_pos c γ R hS)
  · intro hγ
    have hK := pow_K_pos c γ R hS
    rw [pow_sqrt_eq c γ R hγ]
    field_simp
    ring
