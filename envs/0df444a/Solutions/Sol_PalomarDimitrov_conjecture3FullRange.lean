-- Prove2me | solution 1 for PalomarDimitrov.conjecture3FullRange
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:06:14.931211+00:00
-- url     : https://prove2.me/submissions/4fc617d5-1502-44b2-96c3-b0531f12a805

import Definitions.Def_FrontierMathLean_DimitrovConjecture1Equality
import Definitions.Def_FrontierMathLean_DimitrovConjecture3Equality
import Definitions.Def_DimitrovConjectures_Solution
import Theorems.Thm_FrontierMathLean_dedekindPsi_one
import Theorems.Thm_FrontierMathLean_dedekindPsi_zero
import Theorems.Thm_FrontierMathLean_dimitrovConjecture3
attribute [local simp] FrontierMathLean.dedekindPsi_one
attribute [local simp] FrontierMathLean.dedekindPsi_zero



set_option autoImplicit false
open Finset
open scoped ArithmeticFunction.sigma
open PalomarDimitrov
namespace PalomarDimitrov
theorem _root_.solution (k n : ℕ) (hk : 1 ≤ k) (hn : 2 ≤ n) :
    (4 * ((n : ℚ) + 1) ^ (2 * k)
          + (((n : ℚ) ^ 2 - 1) ^ k)
          + ((n : ℚ) - 1) ^ (2 * k)) /
        (2 * (((n : ℚ) + 1) ^ (2 * k)
          + (((n : ℚ) ^ 2 - 1) ^ k))) ≤
      (n.totient : ℚ) ^ k /
          ((dedekindPsi n : ℚ) ^ k
            + (sigmaOne n : ℚ) ^ k) +
        (dedekindPsi n : ℚ) ^ k /
          ((n.totient : ℚ) ^ k
            + (sigmaOne n : ℚ) ^ k) +
        (sigmaOne n : ℚ) ^ k /
          ((n.totient : ℚ) ^ k + (dedekindPsi n : ℚ) ^ k) := by
  simpa only [dedekindPsi, FrontierMathLean.dedekindPsi, sigmaOne] using
    FrontierMathLean.dimitrovConjecture3 k n hk hn
end PalomarDimitrov
