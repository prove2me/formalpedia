-- Prove2me | solution 1 for ParallelPostulate.HyperbolicPlane.points_subset_of_cross_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:06:48.45285+00:00
-- url     : https://prove2.me/submissions/adfb6b3b-18fb-41bf-94ed-92e937f6d92d

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
public import Theorems.Thm_ParallelPostulate_Pairs_Dim_dir_ne_zero
public import Theorems.Thm_ParallelPostulate_Pairs_exists_mul_of_cross_eq_zero

set_option autoImplicit true
@[expose] public section
public section
open ParallelPostulate
open ParallelPostulate.HyperbolicPlane
open Pairs
variable {K : Type*} [Field K]
namespace ParallelPostulate.HyperbolicPlane
theorem _root_.solution (L M M' : Dim K) (hL : L.zero ≠ L.one)
    (hM' : M'.zero ≠ M'.one) (h : cross L.dir M.dir = 0) (h' : cross L.dir M'.dir = 0)
    {P : K × K} (hP : P ∈ M.points) (hP' : P ∈ M'.points) : M.points ⊆ M'.points := by
  obtain ⟨l, hl⟩ := exists_mul_of_cross_eq_zero (L.dir_ne_zero hL) h
  obtain ⟨l', hl'⟩ := exists_mul_of_cross_eq_zero (L.dir_ne_zero hL) h'
  have hl'0 : l' ≠ 0 := by
    rintro rfl
    apply M'.dir_ne_zero hM'
    rw [hl']
    simp
  obtain ⟨p, rfl⟩ := hP
  obtain ⟨p', hp'⟩ := hP'
  rintro _ ⟨x, rfl⟩
  refine ⟨p' + (x - p) * l / l', ?_⟩
  have hy : (x - p) * l / l' * l' = (x - p) * l := div_mul_cancel₀ _ hl'0
  have e1 := congrArg Prod.fst hp'
  have e2 := congrArg Prod.snd hp'
  have l1 := congrArg Prod.fst hl
  have l2 := congrArg Prod.snd hl
  have l1' := congrArg Prod.fst hl'
  have l2' := congrArg Prod.snd hl'
  simp only [Dim.pt, Dim.dir] at e1 e2 l1 l2 l1' l2'
  apply Prod.ext
  · simp only [Dim.pt]
    linear_combination e1 - (x - p) * l1 + (x - p) * l / l' * l1'
      + (L.one.1 - L.zero.1) * hy
  · simp only [Dim.pt]
    linear_combination e2 - (x - p) * l2 + (x - p) * l / l' * l2'
      + (L.one.2 - L.zero.2) * hy
end ParallelPostulate.HyperbolicPlane
