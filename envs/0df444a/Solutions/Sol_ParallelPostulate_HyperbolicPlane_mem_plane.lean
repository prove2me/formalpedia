-- Prove2me | solution 1 for ParallelPostulate.HyperbolicPlane.mem_plane
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:04:24.928066+00:00
-- url     : https://prove2.me/submissions/dcec488a-4d7e-4395-8164-cd2706810bcf

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
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
omit [IsStrictOrderedRing K]
namespace ParallelPostulate.HyperbolicPlane
theorem _root_.solution {κ : K} {p : K × K} : p ∈ plane κ ↔ 0 < 1 + κ * (p.1 ^ 2 + p.2 ^ 2) :=
  Iff.rfl
end ParallelPostulate.HyperbolicPlane
