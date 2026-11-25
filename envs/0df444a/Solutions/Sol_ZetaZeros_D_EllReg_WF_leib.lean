-- Prove2me | solution 1 for ZetaZeros.D.EllReg.WF.leib
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:34:58.853615+00:00
-- url     : https://prove2.me/submissions/7d70941c-3a8d-455c-9f09-b52d68f865dc

import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCut
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_WeakFourier
import Theorems.Thm_ZetaZeros_D_EllReg_WF_dw_cons
import Theorems.Thm_ZetaZeros_D_EllReg_WF_contDiff_dw
import Theorems.Thm_ZetaZeros_D_EllReg_WF_Dk_add
import Theorems.Thm_ZetaZeros_D_EllReg_WF_Dk_mul
import Theorems.Thm_ZetaZeros_D_EllReg_WF_contDiff_ev
import Theorems.Thm_ZetaZeros_D_EllReg_WF_ev_cons
import Theorems.Thm_ZetaZeros_D_EllReg_WF_ev_append
import Theorems.Thm_ZetaZeros_D_EllReg_WF_Dk_ev
import Theorems.Thm_ZetaZeros_D_EllReg_WF_lb_good

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ZetaZeros ZetaZeros.D ZetaZeros.D.EllReg
open MeasureTheory Metric Filter Topology
open scoped ContDiff FourierTransform ENNReal
noncomputable section
open ZetaZeros.D.EllReg.WF
variable {d : ℕ}
namespace ZetaZeros.D.EllReg.WF
theorem _root_.solution {f : E d → ℂ} (hf : ContDiff ℝ ∞ f) : ∀ (w : List (Fin d)) (g : E d → ℂ), ContDiff ℝ ∞ g →
    dw w (fun z => f z * g z) = fun y => f y * dw w g y + ev (lb w f) g y
  | [], g, hg => by funext y; simp [dw, lb, ev]
  | k :: w, g, hg => by
    have hgood := lb_good hf isClosed_univ (by simp) w
    have hc : ∀ p ∈ lb w f, ContDiff ℝ ∞ p.2 := fun p hp => (hgood p hp).2.1
    funext y
    rw [dw_cons, solution hf w g hg, Dk_add (hf.mul (contDiff_dw hg w)) (contDiff_ev hc hg),
      Dk_mul hf (contDiff_dw hg w), Dk_ev hc hg]
    simp only [lb, ev_cons, ev_append, dw_cons]
    ring
end ZetaZeros.D.EllReg.WF
