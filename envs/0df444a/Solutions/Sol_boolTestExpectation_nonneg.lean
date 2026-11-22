-- Prove2me | solution 1 for boolTestExpectation_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:32:44.598502+00:00
-- url     : https://prove2.me/submissions/d6cc28f4-7799-4ebf-82f2-2764d880027c

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
theorem _root_.solution {H : Type*} [Fintype H]
    (μ : FinitePMF H) (f : H → Bool) :
    0 ≤ boolTestExpectation μ f :=
  Finset.sum_nonneg fun h _ =>
    mul_nonneg (μ.prob_nonneg h) (by simp only; split_ifs <;> norm_num)
