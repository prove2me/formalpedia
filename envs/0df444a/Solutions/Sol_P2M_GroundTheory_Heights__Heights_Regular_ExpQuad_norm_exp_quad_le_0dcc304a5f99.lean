-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Regular_ExpQuad_norm_exp_quad_le_0dcc304a5f99
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:49:24.999231+00:00
-- url     : https://prove2.me/submissions/2bd8150d-c50c-4c84-bea5-9799bda4cf8b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_StRiemannSlices
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_StPuncturedExpOrder
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_StLogCoverDescent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PExpExtension

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Regular
open Metric Filter Topology Matrix
noncomputable section
open GroundTheory.Heights₂.Heights.Regular.ExpQuad
variable {n a g : ℕ} (P : PeriodPolydisc n a g) (v : Fin g → ℤ)
namespace GroundTheory.Heights₂.Heights.Regular.ExpQuad
theorem _root_.solution (w : Fin n → ℂ) (hw : w ∈ logCover P.a_le) :
    ‖Complex.exp (2 * Real.pi * Complex.I * qf (P.τ w) v)‖ ≤ 1 := by
  rw [Complex.norm_exp, Real.exp_le_one_iff]
  have hpos := (P.im_posDef w hw).posSemidef.dotProduct_mulVec_nonneg (fun k => (v k : ℝ))
  have him : (qf (P.τ w) v).im =
      star (fun k => (v k : ℝ)) ⬝ᵥ ((P.τ w).map Complex.im *ᵥ fun k => (v k : ℝ)) := by
    simp [qf, dotProduct, mulVec, Complex.im_sum, Complex.mul_im, Complex.re_sum]
  have hre : (2 * Real.pi * Complex.I * qf (P.τ w) v).re = -(2 * Real.pi * (qf (P.τ w) v).im) := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [hre, him]
  have := Real.pi_pos
  nlinarith
end GroundTheory.Heights₂.Heights.Regular.ExpQuad
