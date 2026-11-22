-- Prove2me | solution 1 for ParallelPostulate.HyperbolicPlane.Between.ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:05:55.423933+00:00
-- url     : https://prove2.me/submissions/400d8c70-6af5-4b80-b884-6955d97f1b0d

module
public import Mathlib.Algebra.Ring.Prod
public import Mathlib.Data.Real.Basic
public import Mathlib.Order.Interval.Set.Infinite
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Definitions.Def_LeanPool_ParallelPostulate_Geometry
public import Theorems.Thm_ParallelPostulate_Pairs_Dim_pt_zero
public import Theorems.Thm_ParallelPostulate_Pairs_Dim_pt_one
public import Theorems.Thm_ParallelPostulate_Pairs_Dim_pt_injective
public import Theorems.Thm_ParallelPostulate_HyperbolicPlane_Between_symm

set_option autoImplicit true
@[expose] public section
public section
open ParallelPostulate
open ParallelPostulate.HyperbolicPlane
open Pairs
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
namespace ParallelPostulate.HyperbolicPlane
namespace Between
theorem _root_.solution {A B C : K × K} (h : Between A B C) : A ≠ B ∧ B ≠ C ∧ A ≠ C := by
  obtain ⟨hAC, u, h0, h1, rfl⟩ := h
  have hinj := (Dim.mk A C).pt_injective hAC
  refine ⟨?_, ?_, hAC⟩
  · intro h'
    have h2 := hinj ((Dim.mk A C).pt_zero.trans h')
    linarith
  · intro h'
    have h2 := hinj (h'.trans (Dim.mk A C).pt_one.symm)
    linarith
end Between
end ParallelPostulate.HyperbolicPlane
