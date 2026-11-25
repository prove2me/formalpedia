-- Prove2me | solution 1 for PalomarDimitrov.conjecture1EqualityIffPrime
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:06:23.466459+00:00
-- url     : https://prove2.me/submissions/18327bdf-60af-4372-b6b0-2c748ec13941

import Definitions.Def_FrontierMathLean_DimitrovConjecture1Equality
import Definitions.Def_FrontierMathLean_DimitrovConjecture3Equality
import Definitions.Def_DimitrovConjectures_Solution
import Theorems.Thm_FrontierMathLean_dedekindPsi_one
import Theorems.Thm_FrontierMathLean_dedekindPsi_zero
import Theorems.Thm_FrontierMathLean_dimitrovConjecture1_eq_iff_prime
attribute [local simp] FrontierMathLean.dedekindPsi_one
attribute [local simp] FrontierMathLean.dedekindPsi_zero



set_option autoImplicit false
open Finset
open scoped ArithmeticFunction.sigma
open PalomarDimitrov
namespace PalomarDimitrov
theorem _root_.solution (k n : ℕ) (hk : 1 ≤ k) (hn : 2 ≤ n) :
    ((5 * ((n : ℚ) ^ 2 - 1) ^ k
          + 2 * ((n : ℚ) + 1) ^ (2 * k)
          + 2 * ((n : ℚ) - 1) ^ (2 * k)) /
        (((n : ℚ) ^ 2 - 1) ^ k) =
      ((n.totient : ℚ) ^ k + (dedekindPsi n : ℚ) ^ k
          + (sigmaOne n : ℚ) ^ k) *
        (((n.totient : ℚ) ^ k)⁻¹ + ((dedekindPsi n : ℚ) ^ k)⁻¹
          + ((sigmaOne n : ℚ) ^ k)⁻¹)) ↔
      n.Prime := by
  simpa only [dedekindPsi, FrontierMathLean.dedekindPsi, sigmaOne] using
    FrontierMathLean.dimitrovConjecture1_eq_iff_prime k n hk hn
end PalomarDimitrov
