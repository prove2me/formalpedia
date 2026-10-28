-- Prove2me | solution 1 for TailOptCaching.ETLRU.marginal_cost_identity
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T03:03:58.047747+00:00
-- url     : https://prove2.me/submissions/a9c76a14-9bf6-4c59-adc4-b1615947eeda

import Mathlib
import Definitions.Def_TailOptCaching_ETLRU_Model

open scoped ENNReal

open TailOptCaching.ETLRU in
theorem solution (P : Params) (hξ : ∃ m : ℕ, P.ξ = m) (i L X : ℕ) :
    ∑' Q : ℕ, P.Qlaw i Q * ENNReal.ofReal ((L : ℝ) + Q - P.ξ - ((X : ℝ) - 1)) =
      tailProb P i L X + ∑' Q : ℕ, P.Qlaw i Q * ENNReal.ofReal ((L : ℝ) + Q - P.ξ - X) := by
  obtain ⟨m, hm⟩ := hξ
  unfold tailProb
  rw [← ENNReal.tsum_add]
  congr 1
  funext Q
  rw [hm]
  by_cases h : (X : ℝ) ≤ (L : ℝ) + Q - m
  · rw [if_pos h]
    have e : (L : ℝ) + Q - m - ((X : ℝ) - 1) = ((L : ℝ) + Q - m - X) + 1 := by ring
    rw [e, ENNReal.ofReal_add (by linarith) (by norm_num), ENNReal.ofReal_one, mul_add, mul_one,
      add_comm]
  · rw [if_neg h, zero_add]
    push_neg at h
    have h1 : L + Q < m + X := by
      have : ((L + Q : ℕ) : ℝ) < ((m + X : ℕ) : ℝ) := by push_cast; linarith
      exact_mod_cast this
    have h2 : ((L + Q + 1 : ℕ) : ℝ) ≤ ((m + X : ℕ) : ℝ) := by exact_mod_cast h1
    push_cast at h2
    rw [ENNReal.ofReal_of_nonpos (by linarith), ENNReal.ofReal_of_nonpos (by linarith)]
