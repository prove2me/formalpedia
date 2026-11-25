-- Prove2me | solution 1 for ZetaZeros.D.EllReg.WD.cmp1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:16:08.90496+00:00
-- url     : https://prove2.me/submissions/9178e9e7-6430-46e7-872f-9b0f8c7cd356

import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCut
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_WeightDiff
import Theorems.Thm_ZetaZeros_D_EllReg_WD_base

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
open ZetaZeros.D.EllReg.WD
variable {d : ℕ}
namespace ZetaZeros.D.EllReg.WD
theorem _root_.solution (c : ℝ) (hc : c ^ 2 ≤ 1) (x y v : E d) (hv : ‖x - y‖ ≤ ‖v‖) :
    1 + c ^ 2 * ‖x‖ ^ 2 ≤ (2 * (1 + ‖v‖ ^ 2)) * (1 + c ^ 2 * ‖y‖ ^ 2) := by
  have h := base c x y
  have ha := norm_nonneg (x - y)
  have hv2 : ‖x - y‖ ^ 2 ≤ ‖v‖ ^ 2 := by
    nlinarith [mul_le_mul hv hv ha (norm_nonneg v)]
  have h3 : c ^ 2 * ‖x - y‖ ^ 2 ≤ ‖v‖ ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.2 hc) (sq_nonneg ‖x - y‖)]
  have hy : 0 ≤ 1 + c ^ 2 * ‖y‖ ^ 2 := by positivity
  calc 1 + c ^ 2 * ‖x‖ ^ 2 ≤ 2 * (1 + c ^ 2 * ‖x - y‖ ^ 2) * (1 + c ^ 2 * ‖y‖ ^ 2) := h
    _ ≤ (2 * (1 + ‖v‖ ^ 2)) * (1 + c ^ 2 * ‖y‖ ^ 2) := by
      apply mul_le_mul_of_nonneg_right _ hy
      linarith
end ZetaZeros.D.EllReg.WD
