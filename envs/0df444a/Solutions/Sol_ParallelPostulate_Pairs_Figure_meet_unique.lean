-- Prove2me | solution 1 for ParallelPostulate.Pairs.Figure.meet_unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:06:44.471008+00:00
-- url     : https://prove2.me/submissions/e78ecc26-1be1-45f3-92f5-ec35afe394dc

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
open ParallelPostulate.Pairs
variable {K : Type*} [Field K]
namespace ParallelPostulate.Pairs
namespace Figure
theorem _root_.solution (F : Figure K) (hne : cross F.b.dir F.c.dir ≠ 0) {t u t' u' : K}
    (h : F.b.pt t = F.c.pt u) (h' : F.b.pt t' = F.c.pt u') : t = t' ∧ u = u' := by
  have hb0 : F.b.zero = F.a.zero := F.a0_eq_b0.symm
  have hc0 : F.c.zero = F.a.one := F.a1_eq_c0.symm
  have e1 := congrArg Prod.fst h
  have e2 := congrArg Prod.snd h
  have e1' := congrArg Prod.fst h'
  have e2' := congrArg Prod.snd h'
  simp only [Dim.pt, Dim.dir, cross, hb0, hc0] at e1 e2 e1' e2' hne
  have ht : (t - t') * ((F.b.one.1 - F.a.zero.1) * (F.c.one.2 - F.a.one.2)
      - (F.b.one.2 - F.a.zero.2) * (F.c.one.1 - F.a.one.1)) = 0 := by
    linear_combination (F.c.one.2 - F.a.one.2) * e1 - (F.c.one.2 - F.a.one.2) * e1'
      - (F.c.one.1 - F.a.one.1) * e2 + (F.c.one.1 - F.a.one.1) * e2'
  have hu : (u - u') * ((F.b.one.1 - F.a.zero.1) * (F.c.one.2 - F.a.one.2)
      - (F.b.one.2 - F.a.zero.2) * (F.c.one.1 - F.a.one.1)) = 0 := by
    linear_combination (F.b.one.2 - F.a.zero.2) * e1 - (F.b.one.2 - F.a.zero.2) * e1'
      - (F.b.one.1 - F.a.zero.1) * e2 + (F.b.one.1 - F.a.zero.1) * e2'
  exact ⟨sub_eq_zero.mp ((mul_eq_zero.mp ht).resolve_right hne),
    sub_eq_zero.mp ((mul_eq_zero.mp hu).resolve_right hne)⟩
end Figure
end ParallelPostulate.Pairs
