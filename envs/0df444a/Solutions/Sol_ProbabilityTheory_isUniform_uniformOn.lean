-- Prove2me | solution 1 for ProbabilityTheory.isUniform_uniformOn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:41:49.598333+00:00
-- url     : https://prove2.me/submissions/d80ede5c-c346-4838-9166-a86d78329b09

module
public import Mathlib.Probability.IdentDistrib
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_FiniteRange_Defs
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Data_Set_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_UniformOn
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Uniform
public import Theorems.Thm_ProbabilityTheory_uniformOn_apply_eq_zero


set_option autoImplicit true
@[expose] public section
public section
open Function MeasureTheory Measure Set
open scoped ENNReal
open ProbabilityTheory
universe uΩ uS uT uU
variable {Ω : Type uΩ} {S : Type uS} {T : Type uT} [mΩ : MeasurableSpace Ω]
  {X : Ω → S} {Y : Ω → T} {μ : Measure Ω} {H : Set S}
namespace ProbabilityTheory
theorem _root_.solution [MeasurableSingletonClass Ω] {A : Set Ω} :
    IsUniform A id (uniformOn A) := by
  constructor
  · intro x hx y hy
    have h'x : {x} ∩ A = {x} := by ext y; simp (config := {contextual := true}) [hx]
    have h'y : {y} ∩ A = {y} := by ext y; simp (config := {contextual := true}) [hy]
    simp [uniformOn, cond, h'x, h'y]
  · exact uniformOn_apply_eq_zero (by simp)
end ProbabilityTheory
