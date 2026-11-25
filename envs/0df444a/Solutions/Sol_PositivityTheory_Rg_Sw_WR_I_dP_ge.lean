-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.I.dP_ge
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:20:44.256635+00:00
-- url     : https://prove2.me/submissions/19b530cd-5954-4daa-b8c9-02eb892d055a

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_Integr
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_I_one_add_sum_le_prod
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_I_dP_eq_prod

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
theorem _root_.solution (y : E n) : 1 + ∑ a, ∑ b, y a b ^ 2 ≤ dP y := by
  obtain ⟨h1, h2⟩ := dP_eq_prod y
  rw [h1, h2]
  exact one_add_sum_le_prod _ _ fun i => sq_nonneg _
end PositivityTheory.Rg.Sw.WR.I
