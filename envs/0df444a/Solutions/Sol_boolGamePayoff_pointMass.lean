-- Prove2me | solution 1 for boolGamePayoff_pointMass
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:43:14.980811+00:00
-- url     : https://prove2.me/submissions/d660b48f-f6b0-40ec-a72e-02d772cb9bf2

module
public import Definitions.Def_LeanPool_FormalLearningTheory_PureMath_KLDivergence
public import Mathlib.Algebra.BigOperators.Field
public import Definitions.Def_LeanPool_FormalLearningTheory_PureMath_ApproxMinimax

set_option autoImplicit true
@[expose] public section
public section
open Finset
noncomputable section
theorem _root_.solution {R C : Type*} [Fintype R] [DecidableEq R]
    (M : R → C → Bool) (r₀ : R) (c : C) :
    boolGamePayoff M (pointMassPMF r₀) c = if M r₀ c then 1 else 0 := by
  simp only [boolGamePayoff, pointMassPMF]
  conv_lhs =>
    arg 2; ext r
    rw [show (if r = r₀ then (1 : ℝ) else 0) * (if M r c then (1 : ℝ) else 0) =
      if r = r₀ then (if M r c then 1 else 0) else 0 from by
        split_ifs <;> simp]
  simp
