-- Prove2me | solution 1 for PebblingLean.Hypercube.Paper.optimalPebblingNumber_theta
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:17:38.367849+00:00
-- url     : https://prove2.me/submissions/6b2b83d4-904a-448d-b04b-1798cb216ab0

module
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundParameters
public import Definitions.Def_LeanPool_PebblingLean_LowerBound
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_PebblingLean_Paper
public import Theorems.Thm_PebblingLean_Hypercube_Paper_CLean_pos
public import Theorems.Thm_PebblingLean_Hypercube_Paper_bounds

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
open PebblingLean.Hypercube.Paper
open Pebbling
namespace PebblingLean.Hypercube.Paper
theorem _root_.solution :
    ∃ C : ℝ, 0 < C ∧
      ∀ n : ℕ,
        ((4 : ℝ) / 3) ^ n ≤ (optimalPebblingNumber n : ℝ) ∧
          (optimalPebblingNumber n : ℝ) ≤
            C * (((4 : ℝ) / 3) ^ n) := by
  exact ⟨CLean, CLean_pos, fun n => bounds n⟩
end PebblingLean.Hypercube.Paper
