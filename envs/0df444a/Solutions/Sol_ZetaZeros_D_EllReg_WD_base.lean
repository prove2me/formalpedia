-- Prove2me | solution 1 for ZetaZeros.D.EllReg.WD.base
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:00:31.706781+00:00
-- url     : https://prove2.me/submissions/1eafb0fb-8cf2-43a8-9afb-27a8d11b1d44

import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCut
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_WeightDiff

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
theorem _root_.solution (c : ℝ) (x y : E d) :
    1 + c ^ 2 * ‖x‖ ^ 2 ≤ 2 * (1 + c ^ 2 * ‖x - y‖ ^ 2) * (1 + c ^ 2 * ‖y‖ ^ 2) := by
  have h1 : ‖x‖ ≤ ‖x - y‖ + ‖y‖ := by
    calc ‖x‖ = ‖(x - y) + y‖ := by rw [sub_add_cancel]
      _ ≤ ‖x - y‖ + ‖y‖ := norm_add_le _ _
  have ha := norm_nonneg (x - y)
  have hb := norm_nonneg y
  have hx := norm_nonneg x
  have hc := sq_nonneg c
  have hsq : ‖x‖ ^ 2 ≤ 2 * ‖x - y‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
    nlinarith [sq_nonneg (‖x - y‖ - ‖y‖), mul_le_mul h1 h1 hx (add_nonneg ha hb)]
  nlinarith [mul_le_mul_of_nonneg_left hsq hc,
    mul_nonneg (mul_nonneg hc hc) (mul_nonneg (sq_nonneg ‖x - y‖) (sq_nonneg ‖y‖))]
end ZetaZeros.D.EllReg.WD
