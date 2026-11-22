-- Prove2me | solution 1 for P2M_NemytskiiLebesgue_eLpNorm__norm_rpow_div_eq_f26ae8339226
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:38:02.908505+00:00
-- url     : https://prove2.me/submissions/c3c200e4-66de-4ec1-afba-783764e7c691

module
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Tactic.Cases
public import Mathlib.Tactic.Have
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Basic

set_option autoImplicit true
@[expose] public section
public section
open NemytskiiLebesgue
open scoped NemytskiiLebesgue
open MeasureTheory
open scoped ENNReal
open scoped ENNReal
open scoped RealInnerProductSpace
open MeasureTheory
namespace NemytskiiLebesgue
theorem _root_.solution
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {D : Type*} [NormedAddCommGroup D] (u : Ω → D)
    {p α : ℝ} (hα : 0 < α) :
    eLpNorm' (‖u ·‖ ^ α) (p / α) μ = (eLpNorm' u p μ) ^ α := by
  rw [eLpNorm'_norm_rpow u (p / α) α hα, div_mul_cancel₀ _ hα.ne']
end NemytskiiLebesgue
