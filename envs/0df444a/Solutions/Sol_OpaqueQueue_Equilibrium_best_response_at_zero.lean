-- Prove2me | solution 1 for OpaqueQueue.Equilibrium.best_response_at_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-30T20:50:51.027581+00:00
-- url     : https://prove2.me/submissions/31edc5ef-106d-4953-b4e2-4ac49036a19a

import Mathlib
import Definitions.Def_OpaqueQueue_Equilibrium_Model
open OpaqueQueue.Equilibrium

theorem solution(P : Params) (hS : P.Standing) : stat P 0 0 = 1 ∧ (∀ n : ℕ, 1 ≤ n → stat P 0 n = 0) ∧ ∀ x : ℝ, IsOptimal P (stat P 0) x ↔ x = 1 := by
  obtain ⟨hl, hm, hC, hpR, hθ⟩ := hS
  have hj : ∀ i, joinProb P 0 i = 0 := by intro i; simp [joinProb]
  have hw0 : weight P 0 0 = 1 := by simp [weight]
  have hw : ∀ k, 1 ≤ k → weight P 0 k = 0 := by
    intro k hk
    unfold weight
    rw [Finset.prod_eq_zero (i := 0) (Finset.mem_range.2 (by omega)) (hj 0)]
    ring
  have hsum : ∑' k, weight P 0 k = 1 := by
    rw [tsum_eq_single 0]
    · exact hw0
    · intro k hk; exact hw k (by omega)
  have hs0 : stat P 0 0 = 1 := by unfold stat; rw [hsum, hw0]; norm_num
  have hsn : ∀ n : ℕ, 1 ≤ n → stat P 0 n = 0 := by
    intro n hn; unfold stat; rw [hw n hn]; simp
  have hobj : ∀ x, obj P (stat P 0) x = P.θ * Real.log (x * Real.exp (v P 0 / P.θ) + 1 - x) := by
    intro x
    unfold obj
    congr 1
    rw [tsum_eq_single 0]
    · rw [hs0, one_mul]
    · intro n hn; rw [hsn n (by omega), zero_mul]
  have hE : 1 < Real.exp (v P 0 / P.θ) := by
    have hv : 0 < v P 0 := by simp only [v, Nat.cast_zero, mul_zero, sub_zero]; linarith
    have : 0 < v P 0 / P.θ := div_pos hv hθ
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.2 this
  set E := Real.exp (v P 0 / P.θ) with hEdef
  refine ⟨hs0, hsn, fun x => ⟨fun h => ?_, fun h => ?_⟩⟩
  · obtain ⟨⟨hx0, hx1⟩, hopt⟩ := h
    by_contra hne
    have hxlt : x < 1 := lt_of_le_of_ne hx1 hne
    have h1 := hopt 1 ⟨by norm_num, le_rfl⟩
    rw [hobj, hobj] at h1
    have hpos : 0 < x * E + 1 - x := by nlinarith
    have hlt : x * E + 1 - x < 1 * E + 1 - 1 := by nlinarith
    have h2 := Real.log_lt_log hpos hlt
    nlinarith [mul_lt_mul_of_pos_left h2 hθ]
  · subst h
    refine ⟨⟨by norm_num, le_rfl⟩, fun y hy => ?_⟩
    rw [hobj, hobj]
    obtain ⟨hy0, hy1⟩ := hy
    have hpos : 0 < y * E + 1 - y := by nlinarith
    have hle : y * E + 1 - y ≤ 1 * E + 1 - 1 := by nlinarith
    exact mul_le_mul_of_nonneg_left (Real.log_le_log hpos hle) hθ.le
