-- Prove2me | solution 1 for OracleRO.ApproxFPL.lemma_7
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T03:03:02.215288+00:00
-- url     : https://prove2.me/submissions/06f614db-6c75-491b-aa67-da996bbe8576

import Mathlib
import Definitions.Def_OracleRO_ApproxFPL_IsApproxLinOracle
import Definitions.Def_OracleRO_ApproxFPL_FPL

open MeasureTheory ProbabilityTheory

open OracleRO.ApproxFPL in
theorem lemma7_aux {n : ℕ} (K : Set (Fin n → ℝ)) (ε : ℝ)
    (M : (Fin n → ℝ) → (Fin n → ℝ)) (hM : IsApproxLinOracle K ε M)
    (f : ℕ → Fin n → ℝ) (T : ℕ) :
    M (prefixSum f T) ⬝ᵥ prefixSum f T - ε * T ≤
      ∑ t ∈ Finset.Icc 1 T, M (prefixSum f t) ⬝ᵥ f t := by
  induction T with
  | zero => simp [prefixSum]
  | succ T ih =>
    have hS : prefixSum f (T + 1) = prefixSum f T + f (T + 1) := by
      unfold prefixSum
      rw [Finset.sum_Icc_succ_top (by omega)]
    rw [Finset.sum_Icc_succ_top (by omega)]
    have h1 := (hM (prefixSum f T)).2 (M (prefixSum f (T + 1))) (hM _).1
    rw [hS] at h1 ⊢
    rw [dotProduct_add]
    rw [dotProduct_comm (M (prefixSum f T)) (prefixSum f T)] at ih
    rw [dotProduct_comm (M (prefixSum f T + f (T + 1))) (prefixSum f T)]
    push_cast
    linarith

open OracleRO.ApproxFPL in
theorem solution {n : ℕ} (K : Set (Fin n → ℝ)) (ε : ℝ) (hε : 0 < ε)
    (M : (Fin n → ℝ) → (Fin n → ℝ)) (hM : IsApproxLinOracle K ε M)
    (f : ℕ → Fin n → ℝ) (T : ℕ) :
    M (prefixSum f T) ⬝ᵥ prefixSum f T - ε * T ≤
      ∑ t ∈ Finset.Icc 1 T, M (prefixSum f t) ⬝ᵥ f t := by
  exact lemma7_aux K ε M hM f T
