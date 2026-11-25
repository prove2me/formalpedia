-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.I.normSq_herm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:52:34.467174+00:00
-- url     : https://prove2.me/submissions/1c63e58e-50d5-46b7-95e8-d0858cb89f88

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_Integr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.I
open PositivityTheory.Rg.Sw
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.WR.I
theorem _root_.solution (y : E n) (i j : Fin n) :
    Complex.normSq (herm y i j) = (y i j ^ 2 + y j i ^ 2) / 2 := by
  simp only [herm, Complex.normSq_apply]
  simp
  ring
end PositivityTheory.Rg.Sw.WR.I
