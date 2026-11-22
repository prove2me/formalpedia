-- Prove2me | solution 1 for ParallelPostulate.HyperbolicPlane.line_through
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:07:47.277277+00:00
-- url     : https://prove2.me/submissions/a34b615e-888a-47dc-8356-d6341588fb8c

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
public import Theorems.Thm_ParallelPostulate_Pairs_Dim_zero_mem
public import Theorems.Thm_ParallelPostulate_Pairs_Dim_one_mem
public import Theorems.Thm_ParallelPostulate_Pairs_Dim_points_eq_through

set_option autoImplicit true
@[expose] public section
public section
open ParallelPostulate
open ParallelPostulate.HyperbolicPlane
open Pairs
variable {K : Type*} [Field K]
namespace ParallelPostulate.HyperbolicPlane
theorem _root_.solution (Pl : Set (K × K)) {A B : K × K} (hA : A ∈ Pl) (hB : B ∈ Pl)
    (hAB : A ≠ B) : ∃! S, IsLine Pl S ∧ A ∈ S ∧ B ∈ S := by
  have hAm : A ∈ (Dim.mk A B).points := (Dim.mk A B).zero_mem
  have hBm : B ∈ (Dim.mk A B).points := (Dim.mk A B).one_mem
  refine ⟨(Dim.mk A B).points ∩ Pl,
    ⟨⟨⟨A, B⟩, hAB, rfl, A, hAm, hA⟩, ⟨hAm, hA⟩, ⟨hBm, hB⟩⟩, ?_⟩
  rintro S ⟨⟨M, -, rfl, -⟩, hAS, hBS⟩
  rw [M.points_eq_through hAS.1 hBS.1 hAB]
end ParallelPostulate.HyperbolicPlane
