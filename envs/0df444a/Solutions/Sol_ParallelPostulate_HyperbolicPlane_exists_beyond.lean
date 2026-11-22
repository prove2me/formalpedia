-- Prove2me | solution 1 for ParallelPostulate.HyperbolicPlane.exists_beyond
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:08:09.951547+00:00
-- url     : https://prove2.me/submissions/64eb7895-12af-429a-934c-7d717807fe5a

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
public import Theorems.Thm_ParallelPostulate_HyperbolicPlane_plane_open_forward

set_option autoImplicit true
@[expose] public section
public section
open ParallelPostulate
open ParallelPostulate.HyperbolicPlane
open Pairs
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
namespace ParallelPostulate.HyperbolicPlane
theorem _root_.solution (κ : K) {A C : K × K} (hAC : A ≠ C) (hC : C ∈ plane κ) :
    ∃ B : K × K, B ∈ plane κ ∧ Between A C B := by
  obtain ⟨s, hs, hB⟩ :=
    plane_open_forward κ ⟨C, (C.1 + (C.1 - A.1), C.2 + (C.2 - A.2))⟩ hC
  have hs1 : 0 < 1 + s := by linarith
  have h1 : 1 / (1 + s) * (1 + s) = 1 := div_mul_cancel₀ _ hs1.ne'
  refine ⟨_, hB, ?_, 1 / (1 + s), div_pos one_pos hs1, ?_, ?_⟩
  · intro h
    apply hAC
    have e1 := congrArg Prod.fst h
    have e2 := congrArg Prod.snd h
    simp only [Dim.pt] at e1 e2
    have k1 : (1 + s) * (C.1 - A.1) = 0 := by linear_combination -e1
    have k2 : (1 + s) * (C.2 - A.2) = 0 := by linear_combination -e2
    apply Prod.ext
    · have h3 := (mul_eq_zero.mp k1).resolve_left hs1.ne'
      linarith
    · have h3 := (mul_eq_zero.mp k2).resolve_left hs1.ne'
      linarith
  · rw [div_lt_one hs1]
    linarith
  · apply Prod.ext
    · simp only [Dim.pt]
      linear_combination (C.1 - A.1) * h1
    · simp only [Dim.pt]
      linear_combination (C.2 - A.2) * h1
end ParallelPostulate.HyperbolicPlane
