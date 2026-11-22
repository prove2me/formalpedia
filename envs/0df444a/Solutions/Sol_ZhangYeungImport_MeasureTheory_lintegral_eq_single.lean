-- Prove2me | solution 1 for ZhangYeungImport.MeasureTheory.lintegral_eq_single
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:29:52.125123+00:00
-- url     : https://prove2.me/submissions/bef5ea1c-fba8-4160-8274-8d52f09e6d27

module
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Integral_Lebesgue_Countable

set_option autoImplicit true
@[expose] public section
public section
open ENNReal
open MeasureTheory
variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {s : Set α}
variable [MeasurableSingletonClass α]
namespace MeasureTheory
theorem _root_.solution (μ : Measure α) (a : α) (f : α → ℝ≥0∞) (ha : ∀ b ≠ a,
  f b = 0) :
    ∫⁻ x, f x ∂μ = f a * μ {a} := by
  rw [← lintegral_add_compl f (A := {a}) (MeasurableSet.singleton a), lintegral_singleton,
    setLIntegral_congr_fun (g := fun _ ↦ 0) (MeasurableSet.compl (MeasurableSet.singleton a)),
    lintegral_zero, add_zero]
  simp +contextual [Set.EqOn, ha]
end MeasureTheory
