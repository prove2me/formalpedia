-- Prove2me | solution 1 for ZetaZeros.D.EllReg.WD.om_shift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:27:26.281698+00:00
-- url     : https://prove2.me/submissions/4fe394a4-ead2-4aa0-b7a3-2369bad843b3

import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCut
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_WeightDiff
import Theorems.Thm_ZetaZeros_D_EllReg_WD_pow_cmp
import Theorems.Thm_ZetaZeros_D_EllReg_WD_cmp1

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
theorem _root_.solution (s M ε : ℝ) (hM : 0 ≤ M) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (ζ η v : E d)
    (hv : ‖ζ - η‖ ≤ ‖v‖) :
    om s M ε ζ ≤ (2 * (1 + ‖v‖ ^ 2)) ^ (|s / 2| + M / 2) * om s M ε η := by
  have hA1 : (1 : ℝ) ≤ 2 * (1 + ‖v‖ ^ 2) := by nlinarith [sq_nonneg ‖v‖]
  have hA0 : (0 : ℝ) < 2 * (1 + ‖v‖ ^ 2) := by linarith
  have hv' : ‖η - ζ‖ ≤ ‖v‖ := by rw [norm_sub_rev]; exact hv
  have hε2 : ε ^ 2 ≤ 1 := by nlinarith
  have hone : (1 : ℝ) ^ 2 ≤ 1 := by norm_num
  have P1 := cmp1 1 hone ζ η v hv
  have P2 := cmp1 1 hone η ζ v hv'
  have Q1 := cmp1 ε hε2 ζ η v hv
  have Q2 := cmp1 ε hε2 η ζ v hv'
  simp only [one_pow, one_mul] at P1 P2
  have hζ : (0 : ℝ) < 1 + ‖ζ‖ ^ 2 := by positivity
  have hη : (0 : ℝ) < 1 + ‖η‖ ^ 2 := by positivity
  have hζε : (0 : ℝ) < 1 + ε ^ 2 * ‖ζ‖ ^ 2 := by positivity
  have hηε : (0 : ℝ) < 1 + ε ^ 2 * ‖η‖ ^ 2 := by positivity
  have F1 := pow_cmp (s / 2) hζ hη hA1 P1 P2
  have F2 := pow_cmp (-(M / 2)) hζε hηε hA1 Q1 Q2
  rw [abs_neg, abs_of_nonneg (by linarith : (0 : ℝ) ≤ M / 2)] at F2
  unfold ZetaZeros.D.EllReg.om
  calc _ ≤ ((2 * (1 + ‖v‖ ^ 2)) ^ |s / 2| * (1 + ‖η‖ ^ 2) ^ (s / 2)) *
        ((2 * (1 + ‖v‖ ^ 2)) ^ (M / 2) * (1 + ε ^ 2 * ‖η‖ ^ 2) ^ (-(M / 2))) :=
        mul_le_mul F1 F2 (by positivity) (by positivity)
    _ = _ := by rw [Real.rpow_add hA0]; ring
end ZetaZeros.D.EllReg.WD
