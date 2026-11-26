-- Prove2me | solution 1 for PVM.Represents.proj_eq_on_measurable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:13:54.373683+00:00
-- url     : https://prove2.me/submissions/8d051768-49b8-440a-a6de-7c0a2f41079e

import Definitions.Def_Spectral_Spectral_Uniqueness
import Definitions.Def_Spectral_Spectral_Intrinsic
import Theorems.Thm_PVM_Represents_unboundedIntegral_eq
import Theorems.Thm_spectral_theorem_uniqueness


set_option autoImplicit false
open MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
namespace PVM.Represents
theorem _root_.solution
    {A : E →ₗ.[ℂ] E} (hA : IsSelfAdjoint A)
    {E₁ E₂ : PVM E} (h₁ : E₁.Represents A) (h₂ : E₂.Represents A)
    (S : Set ℝ) (hS : MeasurableSet S) :
    E₁.proj S = E₂.proj S :=
  spectral_theorem_uniqueness A hA E₁ E₂
    (h₁.unboundedIntegral_eq hA) (h₂.unboundedIntegral_eq hA) S hS
end PVM.Represents
