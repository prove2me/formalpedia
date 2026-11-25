-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.B.trace_comboN
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:16:28.663194+00:00
-- url     : https://prove2.me/submissions/0a772550-fb14-481c-9b22-744755dc8f38

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundB
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBound
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_trace_combo

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
    (U * -(c • herm (fun a b => (vkl k l a b).re))).trace +
      Complex.I * (U * -(c • herm (fun a b => (vkl k l a b).im))).trace = -c * U k l := by
  have := trace_combo U c k l
  simp only [Matrix.mul_neg, Matrix.trace_neg]
  linear_combination -this
end PositivityTheory.Rg.Sw.WR.B
