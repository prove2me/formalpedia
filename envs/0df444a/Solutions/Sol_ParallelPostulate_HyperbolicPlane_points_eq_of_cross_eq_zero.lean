-- Prove2me | solution 1 for ParallelPostulate.HyperbolicPlane.points_eq_of_cross_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:07:28.227257+00:00
-- url     : https://prove2.me/submissions/4468ee81-7a87-49a6-8eca-7a28a4f79686

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
public import Theorems.Thm_ParallelPostulate_HyperbolicPlane_points_subset_of_cross_eq_zero

set_option autoImplicit true
@[expose] public section
public section
open ParallelPostulate
open ParallelPostulate.HyperbolicPlane
open Pairs
variable {K : Type*} [Field K]
namespace ParallelPostulate.HyperbolicPlane
theorem _root_.solution (L M M' : Dim K) (hL : L.zero ≠ L.one)
    (hM : M.zero ≠ M.one) (hM' : M'.zero ≠ M'.one) (h : cross L.dir M.dir = 0)
    (h' : cross L.dir M'.dir = 0) {P : K × K} (hP : P ∈ M.points) (hP' : P ∈ M'.points) :
    M.points = M'.points :=
  Set.Subset.antisymm (points_subset_of_cross_eq_zero L M M' hL hM' h h' hP hP')
    (points_subset_of_cross_eq_zero L M' M hL hM h' h hP' hP)
end ParallelPostulate.HyperbolicPlane
