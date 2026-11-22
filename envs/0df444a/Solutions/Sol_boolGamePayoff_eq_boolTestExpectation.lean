-- Prove2me | solution 1 for boolGamePayoff_eq_boolTestExpectation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:37:59.385332+00:00
-- url     : https://prove2.me/submissions/f44f1b3c-9c7c-4c61-852b-95846797556b

module
public import Definitions.Def_LeanPool_FormalLearningTheory_PureMath_ApproxMinimax
public import Mathlib.Combinatorics.SetFamily.Shatter
public import Mathlib.Algebra.BigOperators.Field
public import Definitions.Def_LeanPool_FormalLearningTheory_PureMath_FiniteVCApprox

set_option autoImplicit true
@[expose] public section
public section
open Finset
noncomputable section
theorem _root_.solution
    {R : Type*} [Fintype R]
    {C : Type*} (M : R → C → Bool) (p : FinitePMF R) (c : C) :
    boolGamePayoff M p c = boolTestExpectation p (fun r => M r c) := by
  simp only [boolGamePayoff, boolTestExpectation, trueExpectation]
