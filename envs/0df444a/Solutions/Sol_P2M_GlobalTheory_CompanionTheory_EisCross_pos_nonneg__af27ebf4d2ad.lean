-- Prove2me | solution 1 for P2M_GlobalTheory_CompanionTheory_EisCross_pos_nonneg__af27ebf4d2ad
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:50:21.851698+00:00
-- url     : https://prove2.me/submissions/2f16a725-0eb1-44e2-8997-6b811248c1bb

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CoarseLipschitzExponentialEstimate

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.EisCross
open PositivityTheory.RgEis
namespace GlobalTheory.CompanionTheory.EisCross
theorem _root_.solution {G : Type} [Group G] (Δ P : Subgroup G) (l : G → ℝ) (g : G) : 0 ≤ pos Δ P l g := by
  unfold pos
  exact tsum_nonneg fun _ => (Real.exp_pos _).le
end GlobalTheory.CompanionTheory.EisCross
