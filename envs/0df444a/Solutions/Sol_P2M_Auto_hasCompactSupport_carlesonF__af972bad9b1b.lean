-- Prove2me | solution 1 for P2M_Auto_hasCompactSupport_carlesonF__af972bad9b1b
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:47:20.50332+00:00
-- url     : https://prove2.me/submissions/1843ab4a-4b1e-4fbc-b239-6ad6ad8fbe9f

module
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Definitions.Def_Triangular_Auto_Carleson
public import Theorems.Thm_Auto_carlesonBump_eq_zero
public import Theorems.Thm_Auto_triangularHilbertLinear_apply
attribute [local simp] Auto.triangularHilbertLinear_apply



set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal NNReal Convolution
noncomputable section
namespace Auto
theorem _root_.solution {a : ℝ → ℝ} {A : ℝ} (ha : ∀ x, A < |x| → a x = 0)
    (ν : ℝ → ℝ) (σ : ℝ) : HasCompactSupport (carlesonF₂ a ν σ) := by
  refine HasCompactSupport.intro
    ((isCompact_Icc (a := -(A + 9)) (b := A + 9)).prod (isCompact_Icc (a := -A) (b := A)))
    fun p hp => ?_
  by_cases h₁ : A < |p.2|
  · simp [carlesonF₂, ha _ h₁]
  have h₂ : A + 9 < |p.1| := by
    by_contra h₂
    exact hp ⟨abs_le.mp (not_lt.mp h₂), abs_le.mp (not_lt.mp h₁)⟩
  have h₃ : carlesonBump₁ (p.1 + p.2 / 2) = 0 := by
    apply carlesonBump_eq_zero
    change (9 : ℝ) ≤ |p.1 + p.2 / 2|
    have := abs_sub_abs_le_abs_sub p.1 (-(p.2 / 2))
    rw [sub_neg_eq_add, abs_neg, abs_div, abs_two] at this
    linarith [not_lt.mp h₁, abs_nonneg p.2]
  simp [carlesonF₂, h₃]
end Auto
