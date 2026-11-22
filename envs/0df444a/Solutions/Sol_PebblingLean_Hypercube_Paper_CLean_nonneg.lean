-- Prove2me | solution 1 for PebblingLean.Hypercube.Paper.CLean_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:15:01.616804+00:00
-- url     : https://prove2.me/submissions/02060ca9-9dba-47b4-a377-f04fd661eb2d

module
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundParameters
public import Definitions.Def_LeanPool_PebblingLean_LowerBound
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_PebblingLean_Paper
public import Theorems.Thm_PebblingLean_Hypercube_finiteBaseNormalizedBound_nonneg


set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
open PebblingLean.Hypercube.Paper
open Pebbling
namespace PebblingLean.Hypercube.Paper
theorem _root_.solution : 0 ≤ CLean := by
  unfold CLean
  exact mul_nonneg (Real.exp_nonneg _)
    (finiteBaseNormalizedBound_nonneg _ _)
end PebblingLean.Hypercube.Paper
