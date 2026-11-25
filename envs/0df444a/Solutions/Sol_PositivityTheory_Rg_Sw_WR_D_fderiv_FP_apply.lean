-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.D.fderiv_FP_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:36:54.587039+00:00
-- url     : https://prove2.me/submissions/c833cd5f-3d64-47da-b221-037c80dfb663

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_DerivFA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ContinuousEvXI
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ContinuousEvX
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_DerivF
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_D_Lc_apply
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_D_hasFDerivAt_FP
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_D_integrable_Fd


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.D
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR
variable {m n : ℕ} {ε : Fin m → Bool} {c t : ℝ}
namespace PositivityTheory.Rg.Sw.WR.D
theorem _root_.solution (hI : IntG) (hq : Continuous (qX (n := n) ε)) (hc : 0 < c) (P : PX m n) (y w : E n) :
    fderiv ℝ (FP ε c t P) y w = ∫ x, Fi ε c t P y x * (Complex.I * t) * ((ip w (qX ε x) : ℝ) : ℂ) := by
  rw [(hasFDerivAt_FP hI hq hc P y).fderiv, ContinuousLinearMap.integral_apply (integrable_Fd hI hq hc P y)]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only [Fd, ContinuousLinearMap.smul_apply, Lc_apply, smul_eq_mul, Fi]
end PositivityTheory.Rg.Sw.WR.D
