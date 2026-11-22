-- Prove2me | solution 1 for boolGamePayoff_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:32:16.252295+00:00
-- url     : https://prove2.me/submissions/f1fe7a36-ad71-444a-95cb-febc0139c8fb

module
public import Definitions.Def_LeanPool_FormalLearningTheory_PureMath_KLDivergence
public import Mathlib.Algebra.BigOperators.Field
public import Definitions.Def_LeanPool_FormalLearningTheory_PureMath_ApproxMinimax

set_option autoImplicit true
@[expose] public section
public section
open Finset
noncomputable section
theorem _root_.solution {R C : Type*} [Fintype R]
    (M : R → C → Bool) (p : FinitePMF R) (c : C) :
    0 ≤ boolGamePayoff M p c :=
  Finset.sum_nonneg fun r _ =>
    mul_nonneg (p.prob_nonneg r) (by split_ifs <;> norm_num)
