-- Prove2me | solution 1 for PalomarDimitrov.conjecture1FullRange
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:06:04.60108+00:00
-- url     : https://prove2.me/submissions/6fac76ba-ef86-4a39-be15-453f1914bf71

import Definitions.Def_FrontierMathLean_DimitrovConjecture1Equality
import Definitions.Def_FrontierMathLean_DimitrovConjecture3Equality
import Definitions.Def_DimitrovConjectures_Solution
import Theorems.Thm_FrontierMathLean_dedekindPsi_one
import Theorems.Thm_FrontierMathLean_dedekindPsi_zero
import Theorems.Thm_FrontierMathLean_dimitrovConjecture1
attribute [local simp] FrontierMathLean.dedekindPsi_one
attribute [local simp] FrontierMathLean.dedekindPsi_zero



set_option autoImplicit false
open Finset
open scoped ArithmeticFunction.sigma
open PalomarDimitrov
namespace PalomarDimitrov
theorem _root_.solution (k n : ℕ) (hk : 1 ≤ k) (hn : 2 ≤ n) :
    (5 * ((n : ℚ) ^ 2 - 1) ^ k
          + 2 * ((n : ℚ) + 1) ^ (2 * k)
          + 2 * ((n : ℚ) - 1) ^ (2 * k)) /
        (((n : ℚ) ^ 2 - 1) ^ k) ≤
      ((n.totient : ℚ) ^ k + (dedekindPsi n : ℚ) ^ k
          + (sigmaOne n : ℚ) ^ k) *
        (((n.totient : ℚ) ^ k)⁻¹ + ((dedekindPsi n : ℚ) ^ k)⁻¹
          + ((sigmaOne n : ℚ) ^ k)⁻¹) := by
  simpa only [dedekindPsi, FrontierMathLean.dedekindPsi, sigmaOne] using
    FrontierMathLean.dimitrovConjecture1 k n hk hn
end PalomarDimitrov
