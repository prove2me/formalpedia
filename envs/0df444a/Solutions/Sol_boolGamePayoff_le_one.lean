-- Prove2me | solution 1 for boolGamePayoff_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:43:11.023957+00:00
-- url     : https://prove2.me/submissions/a9b1690f-7311-447d-b9c7-118f91bcc412

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
    boolGamePayoff M p c ≤ 1 := by
  calc boolGamePayoff M p c
      ≤ ∑ r : R, p.prob r := Finset.sum_le_sum fun r _ =>
        mul_le_of_le_one_right (p.prob_nonneg r) (by split_ifs <;> norm_num)
    _ = 1 := p.prob_sum_one
