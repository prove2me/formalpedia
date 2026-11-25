-- Prove2me | solution 1 for P2M_GlobalTheory_CompanionTheory_RgEisGal_ml_re__19bb9b094bcf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:59:50.254141+00:00
-- url     : https://prove2.me/submissions/404388e7-3384-414a-8984-608bf2d1261e

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
theorem _root_.solution : (ml N l).2.re = N - 1 - l.2.re := by simp [chg, aff]; ring
end GlobalTheory.CompanionTheory.RgEisGal
