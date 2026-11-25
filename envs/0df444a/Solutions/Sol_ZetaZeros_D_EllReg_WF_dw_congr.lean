-- Prove2me | solution 1 for ZetaZeros.D.EllReg.WF.dw_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:18:56.443522+00:00
-- url     : https://prove2.me/submissions/1bba7791-039b-4216-baa1-b9a15aa4917c

import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCut
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_WeakFourier
import Theorems.Thm_ZetaZeros_D_EllReg_WF_dw_cons

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
theorem _root_.solution {F G : E d → ℂ} : ∀ (v : List (Fin d)) (y : E d), F =ᶠ[𝓝 y] G → dw v F =ᶠ[𝓝 y] dw v G
  | [], _, h => h
  | k :: v, y, h => by
    have ih := solution v y h
    filter_upwards [ih.eventuallyEq_nhds] with x hx
    simp only [dw_cons, Dk, hx.fderiv_eq]
end ZetaZeros.D.EllReg.WF
