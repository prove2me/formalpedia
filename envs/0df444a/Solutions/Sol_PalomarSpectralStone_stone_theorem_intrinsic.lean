-- Prove2me | solution 1 for PalomarSpectralStone.stone_theorem_intrinsic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:14:59.975923+00:00
-- url     : https://prove2.me/submissions/74cbd7b9-5994-4176-86d3-6b07b5f16645

import Definitions.Def_Spectral_Spectral_Intrinsic
import Definitions.Def_Spectral_Stone_Intrinsic
import Definitions.Def_SpectralStoneSolution
import Theorems.Thm_PalomarSpectralStone_StrongContUnitary_generates_ofRoot
import Theorems.Thm_PalomarSpectralStone_StrongContUnitary_generates_toRoot
import Theorems.Thm_stone_theorem_intrinsic


set_option autoImplicit false
open Function MeasureTheory
open PalomarSpectralStone
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
namespace PalomarSpectralStone
theorem _root_.solution :
    (∀ U : StrongContUnitary E, ∃ A : E →ₗ.[ℂ] E,
      IsSelfAdjoint A ∧ U.Generates A) ∧
    (∀ A : E →ₗ.[ℂ] E, IsSelfAdjoint A →
      ∃ U : StrongContUnitary E, U.Generates A) := by
  refine ⟨fun U ↦ ?_, fun A hA ↦ ?_⟩
  · obtain ⟨A, hA, hGen⟩ := _root_.stone_theorem_intrinsic.1 (StrongContUnitary.toRoot U)
    exact ⟨A, hA, StrongContUnitary.generates_toRoot.mp hGen⟩
  · obtain ⟨U, hGen⟩ := _root_.stone_theorem_intrinsic.2 A hA
    exact ⟨StrongContUnitary.ofRoot U, StrongContUnitary.generates_ofRoot.mpr hGen⟩
end PalomarSpectralStone
