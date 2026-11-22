-- Prove2me | solution 1 for ParallelPostulate.HyperbolicPlane.Between.not_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:07:07.240613+00:00
-- url     : https://prove2.me/submissions/e949c81f-556b-4ee9-9877-064c09094646

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

set_option autoImplicit true
@[expose] public section
public section
open ParallelPostulate
open ParallelPostulate.HyperbolicPlane
open Pairs
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
namespace ParallelPostulate.HyperbolicPlane
namespace Between
theorem _root_.solution {A B C : K × K} (h : Between A B C) : ¬ Between A C B := by
  obtain ⟨hAC, u, hu0, hu1, rfl⟩ := h
  rintro ⟨-, v, hv0, hv1, hv⟩
  have e1 := congrArg Prod.fst hv
  have e2 := congrArg Prod.snd hv
  simp only [Dim.pt] at e1 e2
  have hk : 0 < 1 - v * u := by
    have h' := mul_pos hv0 (sub_pos.mpr hu1)
    nlinarith
  have h1 : (1 - v * u) * (C.1 - A.1) = 0 := by linear_combination -e1
  have h2 : (1 - v * u) * (C.2 - A.2) = 0 := by linear_combination -e2
  apply hAC
  apply Prod.ext
  · have h3 := (mul_eq_zero.mp h1).resolve_left hk.ne'
    linarith
  · have h3 := (mul_eq_zero.mp h2).resolve_left hk.ne'
    linarith
end Between
end ParallelPostulate.HyperbolicPlane
