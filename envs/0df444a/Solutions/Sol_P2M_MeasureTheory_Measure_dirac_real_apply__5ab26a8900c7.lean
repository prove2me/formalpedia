-- Prove2me | solution 1 for P2M_MeasureTheory_Measure_dirac_real_apply__5ab26a8900c7
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:22:25.899033+00:00
-- url     : https://prove2.me/submissions/04bf47eb-f6ce-4f85-bb85-f23abe275e0f

module
public import Mathlib.MeasureTheory.Measure.Dirac
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Measure_Dirac

set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory MeasureTheory.Measure
variable {α : Type*} [MeasurableSpace α] {s : Set α} {a : α}
namespace MeasureTheory.Measure
theorem _root_.solution (a : α) (hs : MeasurableSet s) : (dirac a).real s = s.indicator 1 a := by
  by_cases ha : a ∈ s <;> simp [Measure.real, *]
end MeasureTheory.Measure
