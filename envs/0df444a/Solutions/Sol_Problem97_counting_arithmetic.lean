-- Prove2me | solution 1 for Problem97.counting_arithmetic
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-08T06:06:15.206069+00:00
-- url     : https://prove2.me/submissions/0f0201a8-e188-433d-8bab-7efa841d2873

/- Generated Prove2Me solution by exact Stage 2 source transformations.
   Target command: Erdos9796Proof.P97.CountingArithmetic:511:1656. -/
import Definitions.Def_Erdos9796Counting_Adapter
import Definitions.Def_Erdos9796Counting_Foundation
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

section Erdos9796CountingFragment_Erdos9796Proof_P97_CountingArithmetic

open Problem97

/- Fragment from Erdos9796Proof.P97.CountingArithmetic; source SHA-256 fbcea1f88d69889eb703a9666ba5be87cc47b69941cbca63e4dba5d53dd10763 -/


/-!
# Counting-obstruction arithmetic core (Milestone 3 sub-step)

The arithmetic half of Dumitrescu's `n ≥ 9` bound: given the isosceles
inequality

`6 * n  ≤  (11 * n^2 − 18 * n) / 12`

on natural `n ≥ 3`, conclude `9 ≤ n`.  The geometric half — establishing
the inequality from `HasNEquidistantProperty 4` on a convex point set
— is `p97-dumitrescu-inequality` (still open).

-/




theorem solution {n : ℕ} (hn : 3 ≤ n)
    (h : (6 : ℝ) * n ≤ ((11 : ℝ) * n ^ 2 - 18 * n) / 12) :
    9 ≤ n := by
  by_contra hlt
  have h8 : n ≤ 8 := Nat.lt_succ_iff.mp (Nat.lt_of_not_ge hlt)
  have h8r : (n : ℝ) ≤ 8 := by exact_mod_cast h8
  have hn0 : (0 : ℝ) ≤ n := by exact_mod_cast Nat.zero_le n
  have hnr : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hsq : (n : ℝ) ^ 2 ≤ 8 * n := by nlinarith [hn0, h8r]
  -- Multiply the hypothesis by 12 to clear the divisor.
  have hmul : (72 : ℝ) * n ≤ 11 * n ^ 2 - 18 * n := by
    have htmp := mul_le_mul_of_nonneg_right h (by norm_num : (0 : ℝ) ≤ 12)
    nlinarith [htmp]
  -- Two-sided squeeze: 0 ≤ 11n² − 90n ≤ −6, contradiction.
  have hnonneg : (0 : ℝ) ≤ 11 * n ^ 2 - 90 * n := by nlinarith [hmul]
  have hbad : (11 : ℝ) * n ^ 2 - 90 * n ≤ -6 := by nlinarith [hsq, hnr]
  linarith

end Erdos9796CountingFragment_Erdos9796Proof_P97_CountingArithmetic
