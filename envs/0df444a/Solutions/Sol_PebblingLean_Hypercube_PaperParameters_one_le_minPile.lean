-- Prove2me | solution 1 for PebblingLean.Hypercube.PaperParameters.one_le_minPile
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:55:52.84368+00:00
-- url     : https://prove2.me/submissions/64f44d2a-d67e-4a59-b232-55b2c0ab94c6

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
theorem _root_.solution (n : ℕ) : 1 ≤ minPile n := by
  exact Nat.one_le_pow _ _ (by decide : 0 < 2)
end PebblingLean.Hypercube.PaperParameters
