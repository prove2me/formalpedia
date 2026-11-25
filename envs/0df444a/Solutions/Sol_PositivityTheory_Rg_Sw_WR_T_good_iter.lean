-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.T.good_iter
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:41:08.957372+00:00
-- url     : https://prove2.me/submissions/d30ac1f3-7437-4f91-9694-59e9fc9f63bb

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_DifferentiableOfTop
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_T_good_Delta

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
theorem _root_.solution {f : E n → ℂ} (hf : Good f) (k : ℕ) : Good (Delta^[k] f) := by
  induction k with
  | zero => exact hf
  | succ k ih => rw [Function.iterate_succ_apply']; exact good_Delta ih
end PositivityTheory.Rg.Sw.WR.T
