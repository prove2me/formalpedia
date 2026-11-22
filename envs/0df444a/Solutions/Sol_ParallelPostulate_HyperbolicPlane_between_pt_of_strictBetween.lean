-- Prove2me | solution 1 for ParallelPostulate.HyperbolicPlane.between_pt_of_strictBetween
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:06:34.06298+00:00
-- url     : https://prove2.me/submissions/13fa19a3-2f9e-4624-8d2b-fbf371fb64fc

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
public import Theorems.Thm_ParallelPostulate_Pairs_Dim_pt_injective
public import Theorems.Thm_ParallelPostulate_HyperbolicPlane_Between_symm

set_option autoImplicit true
@[expose] public section
public section
open ParallelPostulate
open ParallelPostulate.HyperbolicPlane
open Pairs
namespace ParallelPostulate.HyperbolicPlane
theorem _root_.solution (M : Dim ℝ) (hM : M.zero ≠ M.one) {a b c : ℝ}
    (h : StrictBetween a c b) : Between (M.pt a) (M.pt c) (M.pt b) := by
  have hab : a ≠ b := by
    rintro rfl
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> linarith
  refine ⟨fun e => hab (M.pt_injective hM e), (c - a) / (b - a), ?_, ?_, ?_⟩
  · rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact div_pos (by linarith) (by linarith)
    · exact div_pos_of_neg_of_neg (by linarith) (by linarith)
  · rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact (div_lt_one (by linarith)).mpr (by linarith)
    · exact (div_lt_one_of_neg (by linarith)).mpr (by linarith)
  · have hba : b - a ≠ 0 := sub_ne_zero.mpr hab.symm
    apply Prod.ext
    · simp only [Dim.pt]
      field_simp
      ring
    · simp only [Dim.pt]
      field_simp
      ring
end ParallelPostulate.HyperbolicPlane
