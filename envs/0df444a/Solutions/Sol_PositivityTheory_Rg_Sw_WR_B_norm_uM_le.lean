-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.B.norm_uM_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:39:27.862308+00:00
-- url     : https://prove2.me/submissions/e673aecf-a841-4559-968b-52426555172c

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundA
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_Am_conjTranspose
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_Bm_mul_Am
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_det_Am_ne
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_uM_eq
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_norm_entry_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open scoped ComplexOrder
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.B
open PositivityTheory.Rg.Sw
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.WR.B
theorem _root_.solution {s : ℂ} (hs : s = 1 ∨ s = -1) (y : E n) (a b : Fin n) : ‖uM s y a b‖ ≤ 1 := by
  rw [uM_eq]
  exact norm_entry_le y (by rw [Am_conjTranspose hs, Bm_mul_Am hs]) (det_Am_ne hs y) a b
end PositivityTheory.Rg.Sw.WR.B
