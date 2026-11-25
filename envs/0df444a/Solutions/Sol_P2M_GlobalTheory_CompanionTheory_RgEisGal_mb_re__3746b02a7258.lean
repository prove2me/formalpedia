-- Prove2me | solution 1 for P2M_GlobalTheory_CompanionTheory_RgEisGal_mb_re__3746b02a7258
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:59:45.395149+00:00
-- url     : https://prove2.me/submissions/4c7ce1cf-0f1f-4a18-8709-903ee692288f

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_DifferentiableAffLine
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ChamberPairThreeFour
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_StripEntireOfFac
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GalleryOfTubesAndCrossing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology PositivityTheory.RgEis
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgEisGal
variable (N : ℝ) (l : ℂ × ℂ)
namespace GlobalTheory.CompanionTheory.RgEisGal
theorem _root_.solution : (mb N l).2.re = 2 * N - 1 - l.1.re - l.2.re := by
  simp [chg, aff]; ring
end GlobalTheory.CompanionTheory.RgEisGal
