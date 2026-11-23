-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.B.contDiff_Am_entry
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:36:21.524843+00:00
-- url     : https://prove2.me/submissions/6be8e7e3-f57c-415d-bf4f-a4911504ec1f

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundB
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_contDiff_herm_entry

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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.B
open PositivityTheory.Rg.Sw
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.WR.B
theorem _root_.solution (s : ℂ) (a b : Fin n) : ContDiff ℝ (⊤ : ℕ∞) (fun y => Am s y a b) := by
  simp only [Am, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  exact contDiff_const.sub (contDiff_const.mul (contDiff_herm_entry a b))
end PositivityTheory.Rg.Sw.WR.B
