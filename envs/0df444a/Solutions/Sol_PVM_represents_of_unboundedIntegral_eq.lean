-- Prove2me | solution 1 for PVM.represents_of_unboundedIntegral_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:12:17.980936+00:00
-- url     : https://prove2.me/submissions/6b40b65b-be8a-471e-a136-1a153146b087

import Definitions.Def_Spectral_Spectral_Uniqueness
import Definitions.Def_Spectral_Spectral_Intrinsic
import Theorems.Thm_PVM_inner_coordinate_unboundedIntegral_self


set_option autoImplicit false
open MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
namespace PVM
theorem _root_.solution (E_pvm : PVM E)
    (A : E →ₗ.[ℂ] E)
    (h : E_pvm.unboundedIntegral ((↑) : ℝ → ℂ)
      Complex.continuous_ofReal.measurable = A) :
    E_pvm.Represents A := by
  subst A
  refine ⟨E_pvm.scalarMeasure, ?_, ?_, ?_⟩
  · intro x S hS
    exact E_pvm.scalarMeasure_apply x S hS
  · intro x
    exact E_pvm.mem_domain_unboundedIntegral
      ((↑) : ℝ → ℂ) Complex.continuous_ofReal.measurable x
  · intro x
    exact E_pvm.inner_coordinate_unboundedIntegral_self x
end PVM
