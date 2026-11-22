-- Prove2me | solution 1 for PebblingLean.Hypercube.Paper.bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:13:59.948969+00:00
-- url     : https://prove2.me/submissions/5b1365f7-6aa2-4aca-a5b5-012b48d1e591

module
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundParameters
public import Definitions.Def_LeanPool_PebblingLean_LowerBound
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_PebblingLean_Paper
public import Theorems.Thm_PebblingLean_Hypercube_Paper_lower_bound_real
public import Theorems.Thm_PebblingLean_Hypercube_Paper_upper_bound

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
open PebblingLean.Hypercube.Paper
open Pebbling
namespace PebblingLean.Hypercube.Paper
theorem _root_.solution (n : ℕ) :
    ((4 : ℝ) / 3) ^ n ≤ (optimalPebblingNumber n : ℝ) ∧
      (optimalPebblingNumber n : ℝ) ≤
        CLean * (((4 : ℝ) / 3) ^ n) :=
  ⟨lower_bound_real n, upper_bound n⟩
end PebblingLean.Hypercube.Paper
