-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.B.det_Bm_mul_det_Am
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:24:12.625542+00:00
-- url     : https://prove2.me/submissions/0389f184-563b-47b4-951d-7b458fdbd734

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundA
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_Bm_mul_Am
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_det_one_add_eq

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
theorem _root_.solution {s : ℂ} (hs : s = 1 ∨ s = -1) (y : E n) :
    (Bm s y).det * (Am s y).det = ((dP y : ℝ) : ℂ) := by
  rw [← det_mul, Bm_mul_Am hs, det_one_add_eq]
end PositivityTheory.Rg.Sw.WR.B
