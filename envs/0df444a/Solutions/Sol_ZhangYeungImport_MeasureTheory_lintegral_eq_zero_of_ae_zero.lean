-- Prove2me | solution 1 for ZhangYeungImport.MeasureTheory.lintegral_eq_zero_of_ae_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:29:47.606973+00:00
-- url     : https://prove2.me/submissions/3a44de51-f75d-49e0-9948-443f31a61698

module
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Integral_Lebesgue_Basic

set_option autoImplicit true
@[expose] public section
public section
open ENNReal
open MeasureTheory
variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {s : Set α}
namespace MeasureTheory
theorem _root_.solution {f : α → ℝ≥0∞} (hs : μ sᶜ = 0) (hf : ∀ x ∈ s,
  f x = 0)
    (hmes : MeasurableSet s) : ∫⁻ x, f x ∂μ = 0 := by
  rw [← lintegral_add_compl f hmes, setLIntegral_measure_zero sᶜ f hs,
    setLIntegral_congr_fun (f := f) (g := fun _ ↦ 0) hmes hf]
  simp
end MeasureTheory
