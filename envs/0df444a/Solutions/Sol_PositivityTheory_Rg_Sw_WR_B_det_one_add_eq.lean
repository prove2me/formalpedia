-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.B.det_one_add_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:18:29.381366+00:00
-- url     : https://prove2.me/submissions/a77ab960-d6de-482d-9bde-6ff1963c762c

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundA
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_posDef_one_add

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
theorem _root_.solution (y : E n) : (1 + herm y * herm y).det = ((dP y : ℝ) : ℂ) := by
  have h := (posDef_one_add y).det_pos
  rw [Complex.lt_def] at h
  apply Complex.ext
  · simp [dP]
  · simp only [Complex.ofReal_im]
    simpa using h.2.symm
end PositivityTheory.Rg.Sw.WR.B
