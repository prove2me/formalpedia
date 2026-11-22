-- Prove2me | solution 1 for PebblingLean.Hypercube.PaperParameters.splitA_real_le_n
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:59:36.284707+00:00
-- url     : https://prove2.me/submissions/7058080e-78c1-477b-8f83-da2252e9997f

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
theorem _root_.solution {K : ℝ} {n : ℕ} :
    (splitA K n : ℝ) ≤ (n : ℝ) := by
  have hnat : splitA K n ≤ n := by
    unfold splitA
    exact Nat.sub_le n (splitM K n)
  exact_mod_cast hnat
end PebblingLean.Hypercube.PaperParameters
