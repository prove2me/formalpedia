-- Prove2me | solution 1 for PVM.scalarContent_union
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:01:31.306908+00:00
-- url     : https://prove2.me/submissions/4165a6c2-cd2b-4b44-9dca-b758c4c8cad4

import Definitions.Def_Spectral_PVM_Integral
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.MeasureTheory.Function.L2Space
import Definitions.Def_Spectral_PVM_Unbounded
import Theorems.Thm_PVM_proj_union


set_option autoImplicit false
open MeasureTheory
open Function
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
namespace PVM
theorem _root_.solution (E_pvm : PVM E) (x : E) {S T : Set ℝ}
    (hS : MeasurableSet S) (hT : MeasurableSet T) (hdisj : Disjoint S T) :
    E_pvm.scalarContent x (S ∪ T) =
      E_pvm.scalarContent x S + E_pvm.scalarContent x T := by
  change (@inner ℂ E _ (E_pvm.proj (S ∪ T) x) x).re =
    (@inner ℂ E _ (E_pvm.proj S x) x).re +
      (@inner ℂ E _ (E_pvm.proj T x) x).re
  rw [E_pvm.proj_union hS hT hdisj, add_apply, inner_add_left, Complex.add_re]
end PVM
