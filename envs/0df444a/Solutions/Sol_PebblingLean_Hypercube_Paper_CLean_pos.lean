-- Prove2me | solution 1 for PebblingLean.Hypercube.Paper.CLean_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:15:56.694175+00:00
-- url     : https://prove2.me/submissions/c1359916-c6ea-4bc2-bb29-69043e43cf1b

module
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundParameters
public import Definitions.Def_LeanPool_PebblingLean_LowerBound
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_PebblingLean_Paper
public import Theorems.Thm_PebblingLean_Hypercube_Paper_CLean_eq_paper_formula
public import Theorems.Thm_PebblingLean_Hypercube_Paper_one_le_CLean_sum

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
open PebblingLean.Hypercube.Paper
open Pebbling
namespace PebblingLean.Hypercube.Paper
theorem _root_.solution : 0 < CLean := by
  rw [CLean_eq_paper_formula]
  exact mul_pos (Real.exp_pos _)
    (lt_of_lt_of_le zero_lt_one one_le_CLean_sum)
end PebblingLean.Hypercube.Paper
