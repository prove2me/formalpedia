-- Prove2me | solution 1 for PVM.represents_iff_unboundedIntegral_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:13:51.024131+00:00
-- url     : https://prove2.me/submissions/240d3c13-14f9-4a66-9948-a983055c8e9e

import Definitions.Def_Spectral_Spectral_Uniqueness
import Definitions.Def_Spectral_Spectral_Intrinsic
import Theorems.Thm_PVM_represents_of_unboundedIntegral_eq
import Theorems.Thm_PVM_Represents_unboundedIntegral_eq

set_option autoImplicit false
open MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
namespace PVM
theorem _root_.solution (E_pvm : PVM E)
    (A : E →ₗ.[ℂ] E) (hA : IsSelfAdjoint A) :
    E_pvm.Represents A ↔
      E_pvm.unboundedIntegral ((↑) : ℝ → ℂ)
        Complex.continuous_ofReal.measurable = A :=
  ⟨fun h ↦ h.unboundedIntegral_eq hA,
    E_pvm.represents_of_unboundedIntegral_eq A⟩
end PVM
