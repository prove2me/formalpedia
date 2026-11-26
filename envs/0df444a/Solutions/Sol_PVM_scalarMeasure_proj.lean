-- Prove2me | solution 1 for PVM.scalarMeasure_proj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:02:02.126644+00:00
-- url     : https://prove2.me/submissions/f02ffd36-41fb-4374-bd8c-63935c9ccdfe

import Definitions.Def_Spectral_PVM_Integral
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.MeasureTheory.Function.L2Space
import Definitions.Def_Spectral_PVM_Unbounded
import Theorems.Thm_PVM_scalarContent_proj

set_option autoImplicit false
open MeasureTheory
open Function
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
namespace PVM
theorem _root_.solution (E_pvm : PVM E) (x : E) (S : Set ℝ)
    (hS : MeasurableSet S) :
    E_pvm.scalarMeasure (E_pvm.proj S x) = (E_pvm.scalarMeasure x).restrict S := by
  apply Measure.ext
  intro T hT
  rw [E_pvm.scalarMeasure_apply (E_pvm.proj S x) T hT,
    E_pvm.scalarContent_proj x S T hS hT, Measure.restrict_apply hT,
    E_pvm.scalarMeasure_apply x (T ∩ S) (hT.inter hS)]
end PVM
