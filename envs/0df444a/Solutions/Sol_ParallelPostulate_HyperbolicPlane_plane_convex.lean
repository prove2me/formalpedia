-- Prove2me | solution 1 for ParallelPostulate.HyperbolicPlane.plane_convex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:05:57.002175+00:00
-- url     : https://prove2.me/submissions/825cecc3-9afa-4552-81aa-db1d2768f936

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
public import Theorems.Thm_ParallelPostulate_HyperbolicPlane_mem_plane
public import Theorems.Thm_ParallelPostulate_HyperbolicPlane_plane_eq_univ

set_option autoImplicit true
@[expose] public section
public section
open ParallelPostulate
open ParallelPostulate.HyperbolicPlane
open Pairs
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
namespace ParallelPostulate.HyperbolicPlane
theorem _root_.solution (κ : K) {A B : K × K} (hA : A ∈ plane κ) (hB : B ∈ plane κ) {u : K}
    (h0 : 0 ≤ u) (h1 : u ≤ 1) : (Dim.mk A B).pt u ∈ plane κ := by
  rcases le_or_gt 0 κ with hκ | hκ
  · rw [plane_eq_univ hκ]
    trivial
  · rw [mem_plane] at hA hB ⊢
    have e : 1 + κ * (((Dim.mk A B).pt u).1 ^ 2 + ((Dim.mk A B).pt u).2 ^ 2)
        = (1 - u) * (1 + κ * (A.1 ^ 2 + A.2 ^ 2)) + u * (1 + κ * (B.1 ^ 2 + B.2 ^ 2))
          + -κ * (u * (1 - u)) * ((B.1 - A.1) ^ 2 + (B.2 - A.2) ^ 2) := by
      simp only [Dim.pt]
      ring
    rw [e]
    have hlast : 0 ≤ -κ * (u * (1 - u)) * ((B.1 - A.1) ^ 2 + (B.2 - A.2) ^ 2) :=
      mul_nonneg (mul_nonneg (by linarith) (mul_nonneg h0 (by linarith))) (by positivity)
    have hB' : 0 ≤ u * (1 + κ * (B.1 ^ 2 + B.2 ^ 2)) := mul_nonneg h0 hB.le
    rcases h1.eq_or_lt with hu | hu
    · rw [hu] at hlast ⊢
      linarith
    · have hA' : 0 < (1 - u) * (1 + κ * (A.1 ^ 2 + A.2 ^ 2)) := mul_pos (by linarith) hA
      linarith
end ParallelPostulate.HyperbolicPlane
