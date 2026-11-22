-- Prove2me | solution 1 for ParallelPostulate.HyperbolicPlane.IsLine.two_points
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:08:13.126165+00:00
-- url     : https://prove2.me/submissions/0527d639-ba32-4f49-8ecb-2793a5480e05

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
public import Theorems.Thm_ParallelPostulate_HyperbolicPlane_IsLine_exists_within

set_option autoImplicit true
@[expose] public section
public section
open ParallelPostulate
open ParallelPostulate.HyperbolicPlane
open Pairs
variable {K : Type*} [Field K]
namespace ParallelPostulate.HyperbolicPlane
namespace IsLine
theorem _root_.solution {Pl S : Set (K × K)} (hopen : OpenAlong Pl) (hS : IsLine Pl S) :
    ∃ A B : K × K, A ≠ B ∧ A ∈ S ∧ B ∈ S := by
  obtain ⟨M, h0, h1, hne, rfl⟩ := hS.exists_within hopen
  exact ⟨M.zero, M.one, hne, ⟨M.zero_mem, h0⟩, ⟨M.one_mem, h1⟩⟩
end IsLine
end ParallelPostulate.HyperbolicPlane
