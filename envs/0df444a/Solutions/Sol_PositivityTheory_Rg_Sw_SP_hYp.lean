-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.SP.hYp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:02:40.271788+00:00
-- url     : https://prove2.me/submissions/5363736b-a2e6-426d-a22f-6190504ee643

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_BridgeSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_BridgeH
import Theorems.Thm_PositivityTheory_Rg_Sw_SP_inv_line
import Theorems.Thm_PositivityTheory_Rg_Sw_SP_mY
import Theorems.Thm_PositivityTheory_Rg_Sw_SP_diff_inv_Y

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Filter Topology
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.SP
open PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.Z
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.SP
theorem _root_.solution : HYp := by
  intro n s x v h a d
  have e : (fun t : ℂ => Yp s (x + t • v) a d) =
      fun t : ℂ => ((1 + (Complex.I * s) • Matrix.of x) + t • ((Complex.I * s) • Matrix.of v))⁻¹ a d := by
    funext t
    simp only [Yp]
    rw [mY s x v t]
  rw [e]
  have := inv_line _ _ h (diff_inv_Y s x v h) a d
  convert this using 1
  simp only [Yp, Matrix.neg_apply, Matrix.smul_apply, smul_eq_mul, Matrix.mul_smul, Matrix.smul_mul]
  ring
end PositivityTheory.Rg.Sw.SP
