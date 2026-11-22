-- Prove2me | solution 1 for ParallelPostulate.Pairs.Figure.meet_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:05:56.308217+00:00
-- url     : https://prove2.me/submissions/1df37dca-dcc5-4cd7-9505-c07d28aa8ca9

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
public import Theorems.Thm_ParallelPostulate_Pairs_cramer_aux

set_option autoImplicit true
@[expose] public section
public section
open ParallelPostulate
open ParallelPostulate.Pairs
variable {K : Type*} [Field K]
namespace ParallelPostulate.Pairs
namespace Figure
theorem _root_.solution (F : Figure K) (hne : cross F.b.dir F.c.dir ≠ 0) :
    F.b.pt (cross F.a.dir F.c.dir / cross F.b.dir F.c.dir)
      = F.c.pt (cross F.a.dir F.b.dir / cross F.b.dir F.c.dir) := by
  have hb0 : F.b.zero = F.a.zero := F.a0_eq_b0.symm
  have hc0 : F.c.zero = F.a.one := F.a1_eq_c0.symm
  apply Prod.ext
  · simp only [Dim.pt, Dim.dir, cross, hb0, hc0] at hne ⊢
    exact cramer_aux _ _ _ _ _ _ _ hne (by ring)
  · simp only [Dim.pt, Dim.dir, cross, hb0, hc0] at hne ⊢
    exact cramer_aux _ _ _ _ _ _ _ hne (by ring)
end Figure
end ParallelPostulate.Pairs
