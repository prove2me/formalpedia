-- Prove2me | solution 1 for PebblingLean.Hypercube.PaperParameters.div_sub_one_le_nat_div_real
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:08:04.751798+00:00
-- url     : https://prove2.me/submissions/c9f2f863-24a1-43c6-b45e-a21ce2a79aef

module
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundLoss
public import Definitions.Def_LeanPool_PebblingLean_LowerBound
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundParameters

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
open PebblingLean.Hypercube.PaperParameters
namespace PebblingLean.Hypercube.PaperParameters
theorem _root_.solution (a d : ℕ) (hd : 0 < d) :
    (a : ℝ) / d - 1 ≤ ((a / d : ℕ) : ℝ) := by
  have hnat : a < d * (a / d + 1) := Nat.lt_mul_div_succ a hd
  have hreal : (a : ℝ) < (d * (a / d + 1) : ℕ) := by
    exact_mod_cast hnat
  rw [Nat.cast_mul, Nat.cast_add, Nat.cast_one] at hreal
  have hdreal : (0 : ℝ) < d := by exact_mod_cast hd
  have hdiv : (a : ℝ) / d < ((a / d : ℕ) : ℝ) + 1 := by
    rw [div_lt_iff₀ hdreal]
    linarith
  linarith
end PebblingLean.Hypercube.PaperParameters
