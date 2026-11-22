-- Prove2me | solution 1 for ParallelPostulate.HyperbolicPlane.plane_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:07:25.324595+00:00
-- url     : https://prove2.me/submissions/172e1e19-a019-427d-ba63-a00b1920ab3a

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
public import Theorems.Thm_ParallelPostulate_HyperbolicPlane_mem_plane

set_option autoImplicit true
@[expose] public section
public section
open ParallelPostulate
open ParallelPostulate.HyperbolicPlane
open Pairs
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
namespace ParallelPostulate.HyperbolicPlane
theorem _root_.solution {κ κ' : K} (h : κ ≤ κ') : plane κ ⊆ plane κ' := by
  intro p hp
  rw [mem_plane] at hp ⊢
  have h' : κ * (p.1 ^ 2 + p.2 ^ 2) ≤ κ' * (p.1 ^ 2 + p.2 ^ 2) :=
    mul_le_mul_of_nonneg_right h (by positivity)
  linarith
end ParallelPostulate.HyperbolicPlane
