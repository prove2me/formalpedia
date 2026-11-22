-- Prove2me | solution 1 for PebblingLean.Hypercube.PaperParameters.loss_le_two_of_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:57:47.262314+00:00
-- url     : https://prove2.me/submissions/07f74fdf-48b9-4d79-ad7c-8b1852c1a53a

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
theorem _root_.solution {n : ℕ} (hn : 0 < n) : loss n ≤ 2 := by
  unfold loss
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hsq : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by
    nlinarith [sq_nonneg ((n : ℝ) - 1)]
  have hinv : (((n : ℝ) ^ 2)⁻¹) ≤ 1 :=
    inv_le_one_of_one_le₀ hsq
  nlinarith
end PebblingLean.Hypercube.PaperParameters
