-- Prove2me | solution 1 for ParallelPostulate.HyperbolicPlane.between_trichotomy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:07:10.974642+00:00
-- url     : https://prove2.me/submissions/be95db42-c590-4214-acaa-8c5230edd8c9

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
public import Theorems.Thm_ParallelPostulate_Pairs_Dim_pt_one
public import Theorems.Thm_ParallelPostulate_HyperbolicPlane_Between_symm

set_option autoImplicit true
@[expose] public section
public section
open ParallelPostulate
open ParallelPostulate.HyperbolicPlane
open Pairs
namespace ParallelPostulate.HyperbolicPlane
theorem _root_.solution {A B C : ℝ × ℝ} (hAB : A ≠ B) (hBC : B ≠ C) (hAC : A ≠ C)
    (hB : B ∈ (Dim.mk A C).points) : Between A B C ∨ Between B A C ∨ Between A C B := by
  obtain ⟨s, rfl⟩ := hB
  have hs0 : s ≠ 0 := by
    rintro rfl
    exact hAB (Dim.pt_zero (Dim.mk A C)).symm
  have hs1 : s ≠ 1 := by
    rintro rfl
    exact hBC (Dim.pt_one (Dim.mk A C))
  rcases lt_or_gt_of_ne hs0 with hneg | hpos
  · have h1s : 0 < 1 - s := by linarith
    refine Or.inr (Or.inl ⟨hBC, -s / (1 - s), div_pos (by linarith) h1s,
      (div_lt_one h1s).mpr (by linarith), ?_⟩)
    apply Prod.ext
    · simp only [Dim.pt]
      field_simp
      ring
    · simp only [Dim.pt]
      field_simp
      ring
  · rcases lt_or_gt_of_ne hs1 with hlt | hgt
    · exact Or.inl ⟨hAC, s, hpos, hlt, rfl⟩
    · refine Or.inr (Or.inr ⟨hAB, 1 / s, by positivity, (div_lt_one hpos).mpr hgt, ?_⟩)
      apply Prod.ext
      · simp only [Dim.pt]
        field_simp
        ring
      · simp only [Dim.pt]
        field_simp
        ring
end ParallelPostulate.HyperbolicPlane
