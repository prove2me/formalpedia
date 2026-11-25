-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HermNorm_norm_ne_zero_0d8080cf190b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:28:08.770428+00:00
-- url     : https://prove2.me/submissions/dc8244e0-102e-4309-ad56-426c8236ad7f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsMahler
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PAdmissibleAENrm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory Matrix
noncomputable section
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights
namespace HermNorm
theorem _root_.solution (h : HermNorm n) {v : Fin n → ℂ} (hv : v ≠ 0) : h.norm v ≠ 0 := by
  intro h0
  apply hv
  have hs : ∑ i, ‖(h.mat *ᵥ v) i‖ ^ 2 = 0 :=
    (Real.sqrt_eq_zero (Finset.sum_nonneg fun i _ => sq_nonneg _)).mp h0
  have hm : h.mat *ᵥ v = 0 := by
    funext i
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg ‖(h.mat *ᵥ v) i‖)).mp hs i
      (Finset.mem_univ i)
    simpa using this
  exact Matrix.eq_zero_of_mulVec_eq_zero h.isUnit_det.ne_zero hm
end HermNorm
end GroundTheory.Heights₂.Heights
