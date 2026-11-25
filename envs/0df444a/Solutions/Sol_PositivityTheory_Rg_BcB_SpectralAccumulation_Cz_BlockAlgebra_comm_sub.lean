-- Prove2me | solution 1 for PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockAlgebra.comm_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:28:46.814547+00:00
-- url     : https://prove2.me/submissions/45761dc0-81bd-48ad-b51a-f668e52344c9

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_InfinitesimalCharacterLimits_LieSumDecompositions_PBlocksAlg

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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.SpectralAccumulation.Cz PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockAlgebra
variable {M : Type} [AddCommGroup M] [Module ℂ M]
namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockAlgebra
theorem _root_.solution {x y : Module.End ℂ M} (h : Commute x y) (c d : ℂ) : Commute (x - c • 1) (y - d • 1) :=
  ((h.sub_right (Commute.smul_right (Commute.one_right _) _)).sub_left
    ((Commute.smul_left (Commute.one_left _) _).sub_right (Commute.smul_right (Commute.one_right _) _)))
end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockAlgebra
