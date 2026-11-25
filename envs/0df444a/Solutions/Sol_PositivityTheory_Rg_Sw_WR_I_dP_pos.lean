-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.I.dP_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:27:31.998643+00:00
-- url     : https://prove2.me/submissions/64de2ea6-0abd-4e1c-9fd5-098ce4303ba9

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_Integr
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_I_dP_ge

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
theorem _root_.solution (y : E n) : 0 < dP y := by
  have h0 : 0 ≤ ∑ a, ∑ b, y a b ^ 2 := Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => sq_nonneg _
  linarith [dP_ge y]
end PositivityTheory.Rg.Sw.WR.I
