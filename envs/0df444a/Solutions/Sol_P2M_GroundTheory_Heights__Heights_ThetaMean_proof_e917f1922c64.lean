-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ThetaMean_proof_e917f1922c64
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:50:49.004257+00:00
-- url     : https://prove2.me/submissions/4f1e8e26-ab9b-4034-95b3-1d2a8cab1877

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsTheta
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ThetaGauss
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PThetaMean
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KThetaMean_continuous_exp_qf_add_4a3dae30bfe7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KTheta_integral_cube_tsum_01bbe72170ef
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KTheta_integral_exp_two_pi_qf_7f0897f8e415
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KTheta_summable_exp_qf_4231a987a485


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
open Matrix Real MeasureTheory
namespace GroundTheory.Heights₂.Heights
namespace ThetaMean
theorem _root_.solution (h : ThetaInnerMean.Statement) : ThetaMean.Statement := by
  intro g X Y a b hY
  set F : (Fin g → ℝ) → ℝ := fun x => exp (-(2 * π) * qf Y (x + a)) with hF
  have hinner : ∀ u₁ : Fin g → ℝ,
      ∫ u₂ in Set.Icc (0 : Fin g → ℝ) 1, thetaNorm X Y a b u₁ u₂ ^ 2 =
        ∑' k : Fin g → ℤ, F (intVec k + u₁) := by
    intro u₁
    rw [h g X Y a b u₁ hY]
    congr 1
    funext k
    simp only [hF, add_right_comm]
  simp_rw [hinner]
  have hs : ∀ u : Fin g → ℝ, Summable fun k : Fin g → ℤ => F (intVec k + u) := by
    intro u
    simp only [hF, add_assoc]
    exact KTheta.summable_exp_qf Y hY (2 * π) (by positivity) (u + a)
  rw [KTheta.integral_cube_tsum F (fun x => (exp_pos _).le)
    (KThetaMean.continuous_exp_qf_add Y (2 * π) a) hs]
  rw [hF, integral_add_right_eq_self (fun x : Fin g → ℝ => exp (-(2 * π) * qf Y x)) a]
  exact KTheta.integral_exp_two_pi_qf Y hY
end ThetaMean
end GroundTheory.Heights₂.Heights
