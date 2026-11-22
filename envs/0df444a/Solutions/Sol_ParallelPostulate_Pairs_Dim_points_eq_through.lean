-- Prove2me | solution 1 for ParallelPostulate.Pairs.Dim.points_eq_through
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:07:08.89095+00:00
-- url     : https://prove2.me/submissions/bce82d4c-d63e-4877-bf22-fca84b94149f

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
public import Theorems.Thm_ParallelPostulate_Pairs_Dim_through_subset

set_option autoImplicit true
@[expose] public section
public section
open ParallelPostulate
open ParallelPostulate.Pairs
variable {K : Type*} [Field K]
namespace ParallelPostulate.Pairs
namespace Dim
theorem _root_.solution (L : Dim K) {A B : K × K} (hA : A ∈ L.points)
    (hB : B ∈ L.points) (hAB : A ≠ B) : L.points = (Dim.mk A B).points := by
  apply Set.Subset.antisymm
  · obtain ⟨s, rfl⟩ := hA
    obtain ⟨s', rfl⟩ := hB
    have hs : s' - s ≠ 0 := by
      intro h
      apply hAB
      rw [sub_eq_zero.mp h]
    rintro _ ⟨x, rfl⟩
    refine ⟨(x - s) / (s' - s), ?_⟩
    have hx : (x - s) / (s' - s) * (s' - s) = x - s := div_mul_cancel₀ _ hs
    apply Prod.ext
    · simp only [Dim.pt]
      linear_combination (L.one.1 - L.zero.1) * hx
    · simp only [Dim.pt]
      linear_combination (L.one.2 - L.zero.2) * hx
  · exact L.through_subset hA hB
end Dim
end ParallelPostulate.Pairs
