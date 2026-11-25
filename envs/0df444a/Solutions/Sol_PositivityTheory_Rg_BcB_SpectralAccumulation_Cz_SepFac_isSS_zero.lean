-- Prove2me | solution 1 for PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.SepFac.isSS_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:57:18.461972+00:00
-- url     : https://prove2.me/submissions/2d2b303f-c3d1-4d8d-83ca-78f785373e47

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_InfinitesimalCharacterLimits_LieSumDecompositions_PSepFac
import Theorems.Thm_PositivityTheory_Rg_BcB_SpectralAccumulation_Cz_SepFac_isSS_algebraMap

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
theorem _root_.solution : IsSS (0 : A) := by simpa using isSS_algebraMap (A := A) 0
end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.SepFac
