-- Prove2me | solution 1 for PebblingLean.Hypercube.PaperParameters.exp_le_one_add_self_add_quadratic_of_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:12:30.535986+00:00
-- url     : https://prove2.me/submissions/9ae84474-d571-4d30-bd53-4b594429bcd7

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
theorem _root_.solution {x : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.exp x ≤ 1 + x + (13 / 18) * x ^ 2 := by
  have h :=
    Real.exp_bound' (x := x) hx0 hx1 (n := 3) (by norm_num)
  have hsum :
      (∑ m ∈ Finset.range 3, x ^ m / (m.factorial : ℝ)) =
        1 + x + x ^ 2 / 2 := by
    norm_num [Finset.sum_range_succ]
  have hx3_le : x ^ 3 ≤ x ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_left hx1 (sq_nonneg x)
    nlinarith
  have htail :
      x ^ 3 * ((3 : ℝ) + 1) / ((Nat.factorial 3 : ℝ) * (3 : ℝ)) ≤
        (2 / 9) * x ^ 2 := by
    norm_num
    nlinarith
  calc
    Real.exp x
        ≤ (∑ m ∈ Finset.range 3, x ^ m / (m.factorial : ℝ)) +
            x ^ 3 * ((3 : ℝ) + 1) /
              ((Nat.factorial 3 : ℝ) * (3 : ℝ)) := h
    _ ≤ 1 + x + x ^ 2 / 2 + (2 / 9) * x ^ 2 := by
          linarith
    _ = 1 + x + (13 / 18) * x ^ 2 := by ring
end PebblingLean.Hypercube.PaperParameters
