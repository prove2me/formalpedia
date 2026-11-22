-- Prove2me | solution 1 for ParallelPostulate.HyperbolicPlane.IsLine.eq_through
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:07:48.345093+00:00
-- url     : https://prove2.me/submissions/0944a342-a769-4e08-9073-edf63edeec19

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
public import Theorems.Thm_ParallelPostulate_Pairs_Dim_points_eq_through

set_option autoImplicit true
@[expose] public section
public section
open ParallelPostulate
open ParallelPostulate.HyperbolicPlane
open Pairs
namespace ParallelPostulate.HyperbolicPlane
namespace IsLine
theorem _root_.solution {κ : ℝ} {S : Set (ℝ × ℝ)} (hS : IsLine (plane κ) S) {D F : ℝ × ℝ}
    (hD : D ∈ S) (hF : F ∈ S) (hDF : D ≠ F) : S = (Dim.mk D F).points ∩ plane κ := by
  obtain ⟨M, -, rfl, -⟩ := hS
  rw [M.points_eq_through hD.1 hF.1 hDF]
end IsLine
end ParallelPostulate.HyperbolicPlane
