-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.T.good_Delta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:33:19.23388+00:00
-- url     : https://prove2.me/submissions/0bff9a10-9977-4fa1-b23d-593d27e16953

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_DifferentiableOfTop
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_T_Delta_eq
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_T_good_FD
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_T_good_sum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix Filter Topology
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.T
open PositivityTheory.Rg.Sw
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.WR.T
theorem _root_.solution {f : E n → ℂ} (hf : Good f) : Good (Delta f) := by
  rw [Delta_eq]
  exact good_sum _ _ _ fun σ _ => good_FD hf _
end PositivityTheory.Rg.Sw.WR.T
