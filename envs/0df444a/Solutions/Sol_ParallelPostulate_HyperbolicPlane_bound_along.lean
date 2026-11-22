-- Prove2me | solution 1 for ParallelPostulate.HyperbolicPlane.bound_along
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:05:17.467837+00:00
-- url     : https://prove2.me/submissions/e9f1f5bf-f810-47b6-8101-2659c27fd411

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
variable {K : Type*} [CommRing K]
namespace ParallelPostulate.HyperbolicPlane
theorem _root_.solution (κ : K) (M : Dim K) (t : K) :
    1 + κ * ((M.pt t).1 ^ 2 + (M.pt t).2 ^ 2)
      = (1 + κ * (M.zero.1 ^ 2 + M.zero.2 ^ 2))
        + (2 * κ * (M.zero.1 * M.dir.1 + M.zero.2 * M.dir.2)) * t
        - (-κ * (M.dir.1 ^ 2 + M.dir.2 ^ 2)) * t ^ 2 := by
  simp only [Dim.pt, Dim.dir]
  ring
end ParallelPostulate.HyperbolicPlane
