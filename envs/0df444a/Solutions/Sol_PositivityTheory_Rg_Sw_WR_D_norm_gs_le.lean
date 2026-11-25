-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.D.norm_gs_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:20:59.168917+00:00
-- url     : https://prove2.me/submissions/0dafaee2-d7be-473b-aa4b-a5f44ce97cba

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_DensDefs
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ImportsBisMore
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ContinuousEvXI
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_D_sq_norm_le_sum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.D
open PositivityTheory.Rg.Sw
variable {m n : ℕ}
namespace PositivityTheory.Rg.Sw.WR.D
theorem _root_.solution (c : ℝ) (hc : 0 < c) (x : Fin m → Fin n → ℂ) : ‖gs c x‖ ≤ Real.exp (-(c * ‖x‖ ^ 2)) := by
  unfold gs
  rw [← Complex.ofReal_neg, Complex.norm_exp_ofReal]
  exact Real.exp_le_exp.2 (by nlinarith [sq_norm_le_sum x])
end PositivityTheory.Rg.Sw.WR.D
