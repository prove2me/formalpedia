-- Prove2me | solution 1 for ParallelPostulate.HyperbolicPlane.IsLine.subset_plane
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:06:31.800174+00:00
-- url     : https://prove2.me/submissions/da34f719-bbe4-4a05-9f9d-c538d919522c

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
namespace ParallelPostulate.HyperbolicPlane
namespace IsLine
theorem _root_.solution {κ : ℝ} {S : Set (ℝ × ℝ)} (hS : IsLine (plane κ) S) :
    S ⊆ plane κ := by
  obtain ⟨M, -, rfl, -⟩ := hS
  exact fun _ hx => hx.2
end IsLine
end ParallelPostulate.HyperbolicPlane
