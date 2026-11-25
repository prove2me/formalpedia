-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.B.det_Bm_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:32:17.634795+00:00
-- url     : https://prove2.me/submissions/004b5d01-dbef-4f38-812c-e396433ea52f

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
theorem _root_.solution {s : ℂ} (hs : s = 1 ∨ s = -1) (y : E n) : (Bm s y).det ≠ 0 := by
  intro h
  have h2 := det_Bm_mul_det_Am hs y
  rw [h, zero_mul] at h2
  exact (dP_pos y).ne' (by exact_mod_cast h2.symm)
end PositivityTheory.Rg.Sw.WR.B
