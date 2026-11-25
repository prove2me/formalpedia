-- Prove2me | solution 1 for ZetaZeros.D.EllReg.gr_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:00:31.396686+00:00
-- url     : https://prove2.me/submissions/f24a45fd-ef1a-4033-996d-5f1e00ad00fa

import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_KernDecay
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_KernDil
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_KernGr

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
namespace ZetaZeros.D.EllReg
theorem _root_.solution {d : ℕ} (b : E d → ℂ) (hb : ContDiff ℝ ∞ b) (L : ℝ) (hL : ∀ x, ‖fderiv ℝ b x‖ ≤ L)
    (x0 y : E d) (r : ℝ) (hr : 0 < r) : ‖b (x0 + r • y) - b x0‖ ≤ L * (r * ‖y‖) := by
  have hd : Differentiable ℝ b := hb.differentiable (by simp)
  have := Convex.norm_image_sub_le_of_norm_fderiv_le (fun x _ => hd x) (fun x _ => hL x)
    convex_univ (Set.mem_univ x0) (Set.mem_univ (x0 + r • y))
  rwa [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hr.le] at this
end ZetaZeros.D.EllReg
