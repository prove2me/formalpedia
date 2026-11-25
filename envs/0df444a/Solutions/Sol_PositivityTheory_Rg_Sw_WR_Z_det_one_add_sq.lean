-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.Z.det_one_add_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:14:47.643266+00:00
-- url     : https://prove2.me/submissions/3b2634f8-f37c-44b2-85fa-c5ec0941a5b8

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsGainSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsGainA
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_Z_sq_smul
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_Z_conjT_X

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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.Z
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.WR.Z
theorem _root_.solution (s : ℂ) (hs : s = 1 ∨ s = -1) (y : E n) :
    (1 + herm y * herm y).det = ((Complex.normSq (1 - (Complex.I * s) • herm y).det : ℝ) : ℂ) := by
  rw [← sq_smul s hs, det_mul, ← conjT_X s hs y, det_conjTranspose, Complex.star_def, Complex.mul_conj]
end PositivityTheory.Rg.Sw.WR.Z
