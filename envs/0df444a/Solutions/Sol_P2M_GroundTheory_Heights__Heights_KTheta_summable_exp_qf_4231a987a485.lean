-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_KTheta_summable_exp_qf_4231a987a485
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:43:49.074385+00:00
-- url     : https://prove2.me/submissions/145d1f10-77f7-485c-9c33-a2f64ebbaac4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KernelsMatrix
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_NormInvSmulMemSphere
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ThetaGauss
import Theorems.Thm_ReciprocityTheory_PTheta_sphereQuadraticPositivity_im_arg
import Theorems.Thm_ReciprocityTheory_PTheta_sphereQuadraticPositivity_norm_eC
import Theorems.Thm_ReciprocityTheory_PTheta_thetaSummable_holds


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open Matrix MeasureTheory Real
open scoped MatrixOrder
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.KTheta
noncomputable section
variable {g : ℕ}
namespace GroundTheory.Heights₂.Heights.KTheta
theorem _root_.solution (Y : Matrix (Fin g) (Fin g) ℝ) (hY : Y.PosDef) (c : ℝ) (hc : 0 < c)
    (v : Fin g → ℝ) : Summable fun k : Fin g → ℤ => exp (-c * qf Y (intVec k + v)) := by
  set τ : Matrix (Fin g) (Fin g) ℂ := Complex.I • Y.map (fun y => (((c / π) * y : ℝ) : ℂ)) with hτ
  have him : τ.map Complex.im = (c / π) • Y := by
    ext i j; simp [hτ]
  have hYt : Yᵀ = Y := by
    have := hY.isHermitian; rw [IsHermitian, conjTranspose_eq_transpose_of_trivial] at this; exact this
  have hdom : τ ∈ ReciprocityTheory.PTheta.ThetaDomain (Fin g) := by
    show (τ.map Complex.im + (τ.map Complex.im)ᵀ).PosDef
    rw [him, transpose_smul, hYt, ← two_smul ℝ, smul_smul]
    exact hY.smul (by positivity)
  have hs := ReciprocityTheory.PTheta.thetaSummable_holds (Fin g) v 0 0 τ hdom
  refine hs.congr fun k => ?_
  unfold ReciprocityTheory.PTheta.thetaTerm
  rw [ReciprocityTheory.PTheta.sphereQuadraticPositivity.norm_eC, ReciprocityTheory.PTheta.sphereQuadraticPositivity.im_arg, him]
  have hw : (fun i => (k i : ℝ) + v i) = intVec k + v := by funext i; simp [intVec]
  rw [hw]
  congr 1
  simp only [qf, smul_mulVec, dotProduct_smul, Pi.zero_apply, Complex.zero_im, smul_eq_mul]
  simp [dotProduct]
  field_simp
end GroundTheory.Heights₂.Heights.KTheta
