-- Prove2me | solution 1 for PVM.scalarContent_proj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:01:21.98181+00:00
-- url     : https://prove2.me/submissions/2517c6c2-e346-49ed-a94f-a5ac103a241a

import Definitions.Def_Spectral_PVM_Integral
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.MeasureTheory.Function.L2Space
import Definitions.Def_Spectral_PVM_Unbounded

set_option autoImplicit false
open MeasureTheory
open Function
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
namespace PVM
theorem _root_.solution (E_pvm : PVM E) (x : E) (S T : Set ℝ)
    (hS : MeasurableSet S) (hT : MeasurableSet T) :
    E_pvm.scalarContent (E_pvm.proj S x) T = E_pvm.scalarContent x (T ∩ S) := by
  rw [E_pvm.scalarContent_eq_norm_sq (E_pvm.proj S x) T hT,
    E_pvm.scalarContent_eq_norm_sq x (T ∩ S) (hT.inter hS),
    E_pvm.inter T S hT hS]
  rfl
end PVM
