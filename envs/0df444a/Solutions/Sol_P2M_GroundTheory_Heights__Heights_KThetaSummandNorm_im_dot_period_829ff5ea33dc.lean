-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_KThetaSummandNorm_im_dot_period_829ff5ea33dc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:01:30.351732+00:00
-- url     : https://prove2.me/submissions/6ef618ac-d8de-4b17-ab74-ee9d88425e66

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsTheta
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PThetaSummandNorm

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
open Matrix Real
noncomputable section
open GroundTheory.Heights₂.Heights.KThetaSummandNorm
namespace GroundTheory.Heights₂.Heights.KThetaSummandNorm
theorem _root_.solution {g : ℕ} (X Y : Matrix (Fin g) (Fin g) ℝ) (w v : Fin g → ℝ) :
    ((fun i => (w i : ℂ)) ⬝ᵥ (periodMatrix X Y *ᵥ fun i => (v i : ℂ))).im = w ⬝ᵥ (Y *ᵥ v) := by
  simp only [dotProduct, mulVec, periodMatrix, Complex.im_sum, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.re_sum, Matrix.add_apply, Matrix.map_apply, Matrix.smul_apply,
    smul_eq_mul, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.I_re, Complex.I_im]
  simp
end GroundTheory.Heights₂.Heights.KThetaSummandNorm
