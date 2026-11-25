-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.B.det_Am_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:32:14.545248+00:00
-- url     : https://prove2.me/submissions/f1c71dad-c3f3-4f88-8742-b025a59ce01b

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundA
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_dP_pos
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_det_Bm_mul_det_Am

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
theorem _root_.solution {s : ℂ} (hs : s = 1 ∨ s = -1) (y : E n) : (Am s y).det ≠ 0 := by
  intro h
  have h2 := det_Bm_mul_det_Am hs y
  rw [h, mul_zero] at h2
  exact (dP_pos y).ne' (by exact_mod_cast h2.symm)
end PositivityTheory.Rg.Sw.WR.B
