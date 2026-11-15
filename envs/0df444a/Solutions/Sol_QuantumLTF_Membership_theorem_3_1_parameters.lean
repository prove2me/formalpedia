-- Prove2me | solution 1 for QuantumLTF.Membership.theorem_3_1_parameters
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-15T03:54:22.234861+00:00
-- url     : https://prove2.me/submissions/54507ebd-a96e-4e30-bdd5-c3235bf8e2f1

import Mathlib
import Definitions.Def_QuantumLTF_Membership_Leps
import Theorems.Thm_QuantumLTF_Membership_Leps_pow_two_pos
import Theorems.Thm_QuantumLTF_Membership_dyadic_bisection_parameters

open QuantumLTF.Membership

theorem solution :
    ∃ C : ℝ, 0 < C ∧ ∀ ε ζ : ℝ, 0 < ε → ε ≤ 1 / 2 → 0 < ζ → ζ < 1 →
      ∃ m q : ℕ,
        Leps ε = (2 : ℝ) ^ m ∧
        ((q + 2 : ℕ) : ℝ) ≤ C * Real.log (Leps ε / ζ) ∧
        ((m + q + 2 : ℕ) : ℝ) ≤ C * Real.log (Leps ε / ζ) ∧
        2 * Leps ε / (2 : ℝ) ^ (q + 1) ≤ ζ := by
  rcases dyadic_bisection_parameters with ⟨C, hC, hdyadic⟩
  refine ⟨C, hC, ?_⟩
  intro ε ζ hε hε' hζ hζ'
  rcases Leps_pow_two_pos ε hε hε' with ⟨m, hm, hL⟩
  rcases hdyadic m hm ζ hζ hζ' with ⟨q, hq, hB, herr⟩
  refine ⟨m, q, hL, ?_, ?_, ?_⟩
  · simpa [hL] using hq
  · simpa [hL] using hB
  · simpa [hL] using herr
