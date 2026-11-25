-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ThetaSummandNorm_proof_183c6dabde9d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:38:08.983868+00:00
-- url     : https://prove2.me/submissions/c30ebf66-d5b9-4c7c-87a9-95edca1e325c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsTheta
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PThetaSummandNorm
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KThetaSummandNorm_im_dot_period_829ff5ea33dc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KThetaSummandNorm_im_dot_real_fce10366cc3b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KThetaSummandNorm_qf_add_272ec1b90821

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
open KThetaSummandNorm
namespace GroundTheory.Heights₂.Heights
namespace ThetaSummandNorm
theorem _root_.solution : ThetaSummandNorm.Statement := by
  intro g X Y a b u₁ u₂ k hY
  set w : Fin g → ℝ := intVec k + a with hw
  have hW : (fun i => ((intVec k i + a i : ℝ) : ℂ)) = fun i => (w i : ℂ) := rfl
  have hzb : (periodMatrix X Y *ᵥ (fun i => (u₁ i : ℂ)) + fun i => (u₂ i : ℂ)) +
      (fun i => (b i : ℂ)) =
      periodMatrix X Y *ᵥ (fun i => (u₁ i : ℂ)) + fun i => ((u₂ + b) i : ℂ) := by
    ext i; simp [add_assoc]
  have hre : (π * Complex.I *
      ((fun i => (w i : ℂ)) ⬝ᵥ (periodMatrix X Y *ᵥ fun i => (w i : ℂ))) +
      2 * π * Complex.I * ((fun i => (w i : ℂ)) ⬝ᵥ
        (periodMatrix X Y *ᵥ (fun i => (u₁ i : ℂ)) + fun i => ((u₂ + b) i : ℂ)))).re =
      -π * qf Y w - 2 * π * (w ⬝ᵥ (Y *ᵥ u₁)) := by
    rw [dotProduct_add]
    simp only [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.re_ofNat, Complex.im_ofNat, Complex.add_im,
      im_dot_period, im_dot_real]
    simp only [qf]
    ring
  unfold thetaSummand
  rw [hW, hzb, Complex.norm_exp, hre, ← Real.exp_add]
  congr 1
  have : intVec k + a + u₁ = w + u₁ := rfl
  rw [this, qf_add Y hY w u₁]
  ring
end ThetaSummandNorm
end GroundTheory.Heights₂.Heights
