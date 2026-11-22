-- Prove2me | solution 1 for ParallelPostulate.HyperbolicPlane.IsLine.exists_within
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:07:46.680224+00:00
-- url     : https://prove2.me/submissions/58d5952f-eaa5-4933-ad6f-6dcd51c9c857

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
public import Theorems.Thm_ParallelPostulate_Pairs_Dim_pt_zero
public import Theorems.Thm_ParallelPostulate_Pairs_Dim_rebase_zero_ne_one
public import Theorems.Thm_ParallelPostulate_Pairs_Dim_pt_injective
public import Theorems.Thm_ParallelPostulate_Pairs_Dim_points_eq_through

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
    ∃ M : Dim K, M.zero ∈ Pl ∧ M.one ∈ Pl ∧ M.zero ≠ M.one ∧ S = M.points ∩ Pl := by
  obtain ⟨M, hM, rfl, A, hAM, hA⟩ := hS
  obtain ⟨r, hr, hB⟩ := hopen (M.rebase A) hA
  have hN := M.rebase_zero_ne_one hM A
  have hAB : A ≠ (M.rebase A).pt r := fun h =>
    hr ((M.rebase A).pt_injective hN ((M.rebase A).pt_zero.trans h)).symm
  have hBM : (M.rebase A).pt r ∈ M.points := by
    obtain ⟨s, rfl⟩ := hAM
    refine ⟨s + r, ?_⟩
    apply Prod.ext
    · simp only [Dim.pt, Dim.rebase]
      ring
    · simp only [Dim.pt, Dim.rebase]
      ring
  exact ⟨⟨A, (M.rebase A).pt r⟩, hA, hB, hAB, by rw [M.points_eq_through hAM hBM hAB]⟩
end IsLine
end ParallelPostulate.HyperbolicPlane
