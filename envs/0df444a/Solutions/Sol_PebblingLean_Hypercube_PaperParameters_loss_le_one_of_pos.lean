-- Prove2me | solution 1 for PebblingLean.Hypercube.PaperParameters.loss_le_one_of_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:07:25.18478+00:00
-- url     : https://prove2.me/submissions/1ae4ea7b-4092-4885-afd4-1e92b486b140

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
theorem _root_.solution {n : ℕ} (hn : 0 < n) : loss n ≤ 1 := by
  unfold loss
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hsq : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by
    nlinarith [sq_nonneg ((n : ℝ) - 1)]
  exact inv_le_one_of_one_le₀ hsq
end PebblingLean.Hypercube.PaperParameters
