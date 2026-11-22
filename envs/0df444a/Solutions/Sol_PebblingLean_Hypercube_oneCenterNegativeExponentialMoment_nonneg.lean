-- Prove2me | solution 1 for PebblingLean.Hypercube.oneCenterNegativeExponentialMoment_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:53:29.562886+00:00
-- url     : https://prove2.me/submissions/3d4fec2c-6416-48c2-8e4b-88ebc6d532f8

module
public import Definitions.Def_LeanPool_PebblingLean_Concentration
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundDelivery
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundProbability

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
open Pebbling
open FiniteProbability
namespace PebblingLean.Hypercube
theorem _root_.solution {n rIn rOut : ℕ}
    (target : HypercubeVertex n) (lam : ℝ) :
    0 ≤ oneCenterNegativeExponentialMoment rIn rOut target lam := by
  classical
  unfold oneCenterNegativeExponentialMoment uniformExpectationReal
  exact div_nonneg
    (Finset.sum_nonneg fun center _hcenter => Real.exp_nonneg _)
    (by positivity)
end PebblingLean.Hypercube
