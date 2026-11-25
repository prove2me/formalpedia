-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.B.trace_combo
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:08:59.863894+00:00
-- url     : https://prove2.me/submissions/6eb7ea8c-8263-4401-a00a-9ecd01ee0c70

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundB
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBound
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_hc_vkl
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_trace_mul_single


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix MvPolynomial
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.B
open PositivityTheory.Rg.Sw
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.WR.B
theorem _root_.solution (U : Matrix (Fin n) (Fin n) ℂ) (c : ℂ) (k l : Fin n) :
    (U * (c • herm (fun a b => (vkl k l a b).re))).trace + Complex.I * (U * (c • herm (fun a b => (vkl k l a b).im))).trace =
      c * U k l := by
  rw [← trace_mul_single U k l, ← hc_vkl k l]
  simp only [Matrix.mul_smul, Matrix.trace_smul, Matrix.mul_add, Matrix.trace_add, smul_eq_mul]
  ring
end PositivityTheory.Rg.Sw.WR.B
