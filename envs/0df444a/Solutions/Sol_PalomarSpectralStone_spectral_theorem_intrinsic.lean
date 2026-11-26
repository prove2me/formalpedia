-- Prove2me | solution 1 for PalomarSpectralStone.spectral_theorem_intrinsic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:18:03.249444+00:00
-- url     : https://prove2.me/submissions/688a7ff8-36cc-4299-aea7-c3f34f9fe280

import Definitions.Def_Spectral_Spectral_Intrinsic
import Definitions.Def_Spectral_Stone_Intrinsic
import Definitions.Def_SpectralStoneSolution
import Theorems.Thm_PalomarSpectralStone_PVM_represents_ofRoot
import Theorems.Thm_PalomarSpectralStone_PVM_represents_toRoot
import Theorems.Thm_PVM_Represents_proj_eq_on_measurable
import Theorems.Thm_spectral_theorem_intrinsic_existence


set_option autoImplicit false
open Function MeasureTheory
open PalomarSpectralStone
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
namespace PalomarSpectralStone
theorem _root_.solution
    (A : E →ₗ.[ℂ] E) (hA : IsSelfAdjoint A) :
    ∃ E_pvm : PVM E,
      E_pvm.Represents A ∧
      ∀ F_pvm : PVM E, F_pvm.Represents A →
        ∀ S : Set ℝ, MeasurableSet S → E_pvm.proj S = F_pvm.proj S := by
  obtain ⟨E_pvm, hRep⟩ := _root_.spectral_theorem_intrinsic_existence A hA
  refine ⟨PVM.ofRoot E_pvm, PVM.represents_ofRoot.mpr hRep, ?_⟩
  intro F_pvm hF S hS
  exact hRep.proj_eq_on_measurable hA (PVM.represents_toRoot.mpr hF) S hS
end PalomarSpectralStone
