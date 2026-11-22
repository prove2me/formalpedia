-- Prove2me | solution 1 for ParallelPostulate.HyperbolicPlane.points_eq_of_two_common
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:07:46.171034+00:00
-- url     : https://prove2.me/submissions/3ca71384-f973-4288-be8b-604d55171d75

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
variable {K : Type*} [Field K]
namespace ParallelPostulate.HyperbolicPlane
theorem _root_.solution (L M : Dim K) {A B : K × K} (hAB : A ≠ B)
    (hA : A ∈ L.points) (hB : B ∈ L.points) (hA' : A ∈ M.points) (hB' : B ∈ M.points) :
    L.points = M.points := by
  rw [L.points_eq_through hA hB hAB, M.points_eq_through hA' hB' hAB]
end ParallelPostulate.HyperbolicPlane
