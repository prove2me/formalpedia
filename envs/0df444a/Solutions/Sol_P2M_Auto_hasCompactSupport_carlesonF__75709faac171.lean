-- Prove2me | solution 1 for P2M_Auto_hasCompactSupport_carlesonF__75709faac171
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:45:29.208803+00:00
-- url     : https://prove2.me/submissions/2de09a66-204d-44f7-a157-2c15a586d8ff

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
    (ν : ℝ → ℝ) (σ : ℝ) : HasCompactSupport (carlesonF₀ a ν σ) := by
  refine HasCompactSupport.intro
    ((isCompact_Icc (a := -A) (b := A)).prod (isCompact_Icc (a := -(A + 2)) (b := A + 2)))
    fun p hp => ?_
  by_cases h₁ : A < |p.1|
  · simp [carlesonF₀, ha _ h₁]
  have h₂ : A + 2 < |p.2| := by
    by_contra h₂
    exact hp ⟨abs_le.mp (not_lt.mp h₁), abs_le.mp (not_lt.mp h₂)⟩
  have h₃ : carlesonBump₀ (p.2 + p.1 / 2) = 0 := by
    apply carlesonBump_eq_zero
    change (2 : ℝ) ≤ |p.2 + p.1 / 2|
    have := abs_sub_abs_le_abs_sub p.2 (-(p.1 / 2))
    rw [sub_neg_eq_add, abs_neg, abs_div, abs_two] at this
    linarith [not_lt.mp h₁, abs_nonneg p.1]
  simp [carlesonF₀, h₃]
end Auto
