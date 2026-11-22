-- Prove2me | solution 1 for ParallelPostulate.HyperbolicPlane.pt_mem_plane_of_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:07:14.830736+00:00
-- url     : https://prove2.me/submissions/4e0ef20b-fe26-46ff-ad3b-96fa870d1d9f

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
public import Theorems.Thm_ParallelPostulate_HyperbolicPlane_plane_convex

set_option autoImplicit true
@[expose] public section
public section
open ParallelPostulate
open ParallelPostulate.HyperbolicPlane
open Pairs
namespace ParallelPostulate.HyperbolicPlane
theorem _root_.solution {κ : ℝ} (M : Dim ℝ) {a b c : ℝ} (ha : M.pt a ∈ plane κ)
    (hb : M.pt b ∈ plane κ) (hac : a ≤ c) (hcb : c ≤ b) : M.pt c ∈ plane κ := by
  rcases hac.eq_or_lt with rfl | hac'
  · exact ha
  have hab : 0 < b - a := by linarith
  have e : M.pt c = (Dim.mk (M.pt a) (M.pt b)).pt ((c - a) / (b - a)) := by
    apply Prod.ext
    · simp only [Dim.pt]
      field_simp
      ring
    · simp only [Dim.pt]
      field_simp
      ring
  rw [e]
  exact plane_convex κ ha hb (div_nonneg (by linarith) hab.le)
    ((div_le_one hab).mpr (by linarith))
end ParallelPostulate.HyperbolicPlane
