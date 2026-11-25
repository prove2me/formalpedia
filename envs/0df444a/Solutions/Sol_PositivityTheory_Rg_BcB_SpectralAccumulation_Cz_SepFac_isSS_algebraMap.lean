-- Prove2me | solution 1 for PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.SepFac.isSS_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:47:25.18858+00:00
-- url     : https://prove2.me/submissions/8df8990d-939d-467f-a77f-9bdfae2f6648

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_InfinitesimalCharacterLimits_LieSumDecompositions_PSepFac
import Theorems.Thm_PositivityTheory_Rg_BcB_SpectralAccumulation_Cz_SepFac_isSS_of_decomp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.SpectralAccumulation.Cz PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.SepFac
variable {A : Type} [Ring A] [Algebra ℂ A]
namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.SepFac
theorem _root_.solution (c : ℂ) : IsSS (algebraMap ℂ A c) :=
  isSS_of_decomp ({()} : Finset Unit) (fun _ => 1) (fun _ => c) (by simp) fun _ _ => by
    rw [mul_one, Algebra.algebraMap_eq_smul_one]
end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.SepFac
