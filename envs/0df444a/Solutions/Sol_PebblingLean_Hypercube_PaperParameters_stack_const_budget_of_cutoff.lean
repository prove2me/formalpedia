-- Prove2me | solution 1 for PebblingLean.Hypercube.PaperParameters.stack_const_budget_of_cutoff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:10:50.017807+00:00
-- url     : https://prove2.me/submissions/26c891b7-7de8-4c4f-9d53-883b524b6d82

module
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundLoss
public import Definitions.Def_LeanPool_PebblingLean_LowerBound
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundParameters
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_stack_linear_margin_nonneg

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
open PebblingLean.Hypercube.PaperParameters
namespace PebblingLean.Hypercube.PaperParameters
theorem _root_.solution {n0 n : ℕ}
    (hn : n0 ≤ n)
    (hcutoff :
      12 * Real.log 2 ≤
        (n0 : ℝ) *
          (Real.log ((4 : ℝ) / 3) - Real.log 2 / 3)) :
    12 * Real.log 2 ≤
      (n : ℝ) *
        (Real.log ((4 : ℝ) / 3) - Real.log 2 / 3) := by
  have hmargin := stack_linear_margin_nonneg
  have hnreal : (n0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hmono :
      (n0 : ℝ) *
          (Real.log ((4 : ℝ) / 3) - Real.log 2 / 3) ≤
        (n : ℝ) *
          (Real.log ((4 : ℝ) / 3) - Real.log 2 / 3) :=
    mul_le_mul_of_nonneg_right hnreal hmargin
  exact hcutoff.trans hmono
end PebblingLean.Hypercube.PaperParameters
