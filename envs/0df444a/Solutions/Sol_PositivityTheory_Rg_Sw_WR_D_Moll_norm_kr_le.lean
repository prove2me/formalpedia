-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.D.Moll.norm_kr_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:51:05.18022+00:00
-- url     : https://prove2.me/submissions/dd556396-cb23-422b-abb0-2510abb7cc99

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_MollIdA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_MollId
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_D_Moll_norm_cexp_It

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.D PositivityTheory.Rg.Sw.WR.D.Moll
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.D
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.WR.D.Moll
theorem _root_.solution (ε t : ℝ) (hε : 0 < ε) (u : E n) : ‖kr ε t u‖ ≤ ∫ y, ‖gam (n := n) ε y‖ := by
  unfold kr
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  congr 1; ext y
  rw [norm_mul, norm_cexp_It, mul_one]
end PositivityTheory.Rg.Sw.WR.D.Moll
