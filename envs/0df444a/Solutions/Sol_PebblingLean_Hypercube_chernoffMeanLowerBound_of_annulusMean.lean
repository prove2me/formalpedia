-- Prove2me | solution 1 for PebblingLean.Hypercube.chernoffMeanLowerBound_of_annulusMean
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:14:28.364647+00:00
-- url     : https://prove2.me/submissions/69cb2a8f-5482-499d-8598-7b13418ee5a4

module
public import Definitions.Def_LeanPool_PebblingLean_Concentration
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundDelivery
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundProbability
public import Theorems.Thm_PebblingLean_Hypercube_chernoffMeanLowerBound_iff_annulusMean

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
open Pebbling
open FiniteProbability
namespace PebblingLean.Hypercube
theorem _root_.solution {n N rIn rOut T : ℕ}
    (hmean : (T : ℚ) ≤ (N : ℚ) * annulusMean n rIn rOut) :
    ChernoffMeanLowerBound n N rIn rOut T :=
  chernoffMeanLowerBound_iff_annulusMean.mpr hmean
end PebblingLean.Hypercube
