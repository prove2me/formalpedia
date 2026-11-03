-- Prove2me | solution 1 for WordRAM.APSPBridge.real_log_pow_le_rpow
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-11-02T20:31:01.338005+00:00
-- url     : https://prove2.me/submissions/1e953aaa-b5db-4358-b68c-75630cab2ef3

import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Asymptotics.Lemmas

open Filter Asymptotics

theorem solution (m : Nat) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ x : ℝ, 2 ≤ x → (Real.log x) ^ m ≤ K * x ^ ε := by
  have hlittle : (fun x : ℝ => Real.log x ^ m) =o[atTop] (fun x : ℝ => x) :=
    Real.isLittleO_pow_log_id_atTop
  have hεm : 0 < ε ^ m := pow_pos hε m
  have hev : ∀ᶠ x : ℝ in atTop, ‖Real.log x ^ m‖ ≤ ε ^ m * ‖x‖ :=
    (Asymptotics.isLittleO_iff.1 hlittle) hεm
  have htend : Tendsto (fun y : ℝ => y ^ ε) atTop atTop := tendsto_rpow_atTop hε
  have hev2 : ∀ᶠ y : ℝ in atTop, ‖Real.log (y ^ ε) ^ m‖ ≤ ε ^ m * ‖y ^ ε‖ :=
    htend.eventually hev
  rw [eventually_atTop] at hev2
  obtain ⟨N, hN⟩ := hev2
  have key : ∀ y : ℝ, max N 1 ≤ y → (Real.log y) ^ m ≤ y ^ ε := by
    intro y hy
    have hy1 : 1 ≤ y := le_trans (le_max_right N 1) hy
    have hypos : 0 < y := lt_of_lt_of_le zero_lt_one hy1
    have hyN : N ≤ y := le_trans (le_max_left N 1) hy
    have h := hN y hyN
    have hlog : Real.log (y ^ ε) = ε * Real.log y := Real.log_rpow hypos ε
    have hlog_nonneg : 0 ≤ Real.log y := Real.log_nonneg hy1
    have hyεpos : 0 < y ^ ε := Real.rpow_pos_of_pos hypos ε
    have h' : ε ^ m * (Real.log y) ^ m ≤ ε ^ m * y ^ ε := by
      simpa [hlog, mul_pow, abs_of_pos hε, abs_of_nonneg hlog_nonneg,
        abs_of_pos hyεpos] using h
    exact le_of_mul_le_mul_left h' hεm
  let K : ℝ := max 1 ((max (Real.log (max (N : ℝ) 2)) 0) ^ m)
  refine ⟨K, ?_, ?_⟩
  · positivity
  · intro x hx
    have hx2 : (2 : ℝ) ≤ x := hx
    have hxε1 : 1 ≤ x ^ ε := Real.one_le_rpow (by linarith) (le_of_lt hε)
    by_cases hxN : max N 1 ≤ x
    · have h := key x hxN
      have hxεpos : 0 < x ^ ε := Real.rpow_pos_of_pos (by linarith) ε
      have hK1 : 1 ≤ K := le_max_left _ _
      calc
        (Real.log x) ^ m ≤ x ^ ε := h
        _ = 1 * x ^ ε := by ring
        _ ≤ K * x ^ ε := mul_le_mul_of_nonneg_right hK1 (le_of_lt hxεpos)
    · have hxN1 : x < max N 1 := lt_of_not_ge hxN
      have hN12 : max (N : ℝ) 1 ≤ max (N : ℝ) 2 := by
        exact max_le_max_left (N : ℝ) (by norm_num : (1 : ℝ) ≤ 2)
      have hxN2 : x ≤ max (N : ℝ) 2 := by linarith
      have hlogx_le : Real.log x ≤ Real.log (max (N : ℝ) 2) := by
        apply Real.log_le_log (by linarith)
        exact hxN2
      have hlogx_nonneg : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
      have hpow_le : (Real.log x) ^ m ≤ (max (Real.log (max (N : ℝ) 2)) 0) ^ m := by
        exact pow_le_pow_left₀ hlogx_nonneg (le_max_of_le_left hlogx_le) m
      have hK_ge : (max (Real.log (max (N : ℝ) 2)) 0) ^ m ≤ K := le_max_right _ _
      calc
        (Real.log x) ^ m ≤ (max (Real.log (max (N : ℝ) 2)) 0) ^ m := hpow_le
        _ ≤ K := hK_ge
        _ = K * 1 := by ring
        _ ≤ K * x ^ ε := by
          apply mul_le_mul_of_nonneg_left hxε1
          positivity
