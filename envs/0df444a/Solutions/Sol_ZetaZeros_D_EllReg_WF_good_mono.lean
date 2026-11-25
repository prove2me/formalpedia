-- Prove2me | solution 1 for ZetaZeros.D.EllReg.WF.good_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:25:16.716262+00:00
-- url     : https://prove2.me/submissions/0d435547-080d-4801-84ba-ac477238733b

import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCut
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_WeakFourier

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ZetaZeros ZetaZeros.D ZetaZeros.D.EllReg
open MeasureTheory Metric Filter Topology
open scoped ContDiff FourierTransform ENNReal
noncomputable section
open ZetaZeros.D.EllReg.WF
variable {d : ℕ}
namespace ZetaZeros.D.EllReg.WF
theorem _root_.solution {k k' : ℕ} {K : Set (E d)} {L : List (List (Fin d) × (E d → ℂ))} (hL : Good k K L)
    (hk : k ≤ k') : Good k' K L := by
  intro p hp
  obtain ⟨h1, h2⟩ := hL p hp
  exact ⟨lt_of_lt_of_le h1 hk, h2⟩
end ZetaZeros.D.EllReg.WF
