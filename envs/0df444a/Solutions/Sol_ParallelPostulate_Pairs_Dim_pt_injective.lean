-- Prove2me | solution 1 for ParallelPostulate.Pairs.Dim.pt_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:04:57.883003+00:00
-- url     : https://prove2.me/submissions/3da77df0-42ce-42ae-a563-37a1d97b1983

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

set_option autoImplicit true
@[expose] public section
public section
open ParallelPostulate
open ParallelPostulate.Pairs
variable {K : Type*} [Field K]
namespace ParallelPostulate.Pairs
namespace Dim
theorem _root_.solution (M : Dim K) (hM : M.zero ≠ M.one) : Function.Injective M.pt := by
  intro s s' h
  have e1 := congrArg Prod.fst h
  have e2 := congrArg Prod.snd h
  simp only [Dim.pt] at e1 e2
  by_contra hne
  have hs : s - s' ≠ 0 := sub_ne_zero.mpr hne
  have h1 : (s - s') * (M.one.1 - M.zero.1) = 0 := by linear_combination e1
  have h2 : (s - s') * (M.one.2 - M.zero.2) = 0 := by linear_combination e2
  exact M.dir_ne_zero hM
    (Prod.ext ((mul_eq_zero.mp h1).resolve_left hs) ((mul_eq_zero.mp h2).resolve_left hs))
end Dim
end ParallelPostulate.Pairs
