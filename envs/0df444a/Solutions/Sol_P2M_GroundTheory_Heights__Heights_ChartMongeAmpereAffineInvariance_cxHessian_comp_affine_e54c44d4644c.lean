-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartMongeAmpereAffineInvariance_cxHessian_comp_affine_e54c44d4644c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:56:17.323367+00:00
-- url     : https://prove2.me/submissions/d578b5e2-82ce-4acb-b23b-082856e240b8

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsSemipositiveOn
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ChartMassAffine
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartMongeAmpereAffineInvariance_cxHessian_eq_sesq_4253c4c2c89e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartMongeAmpereAffineInvariance_sesq_expand_69b1d82df637
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartMongeAmpereAffineInvariance_realCLE_apply_c180c099b79c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartMongeAmpereAffineInvariance_fderiv_fderiv_comp_affine_7e54354380f4

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
open ReciprocityTheory.ChartRestriction.G.Geo Matrix MeasureTheory
noncomputable section
open GroundTheory.Heights₂.Heights.ChartMongeAmpereAffineInvariance
variable {D : ℕ}
namespace GroundTheory.Heights₂.Heights.ChartMongeAmpereAffineInvariance
theorem _root_.solution (φ : (Fin D → ℂ) → ℝ) (c : Fin D → ℂ) (P : Matrix (Fin D) (Fin D) ℂ)
    (hP : P.det ≠ 0) (κ : ℝ) (z : Fin D → ℂ) :
    cxHessian (fun y => φ (c + P *ᵥ y) + κ) z =
      Pᵀ * cxHessian φ (c + P *ᵥ z) * P.map (starRingEnd ℂ) := by
  ext i j
  set L := realCLE P hP
  set H := fderiv ℝ (fderiv ℝ φ) (c + P *ᵥ z)
  have hI : ∀ w, L (Complex.I • w) = Complex.I • L w := fun w => by
    simp only [L, realCLE_apply, Matrix.mulVec_smul]
  have hent : cxHessian (fun y => φ (c + P *ᵥ y) + κ) z i j = sesq H (L (Pi.single i 1)) (L (Pi.single j 1)) := by
    have hg : (fun y => φ (c + P *ᵥ y) + κ) = fun y => φ (c + L y) + κ := rfl
    rw [cxHessian_eq_sesq, hg]
    simp only [sesq, fderiv_fderiv_comp_affine, hI]
    rfl
  rw [hent, sesq_expand]
  simp only [L, realCLE_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul,
    mulVec_single_one]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  have hc : cxHessian φ (c + P *ᵥ z) l k = sesq H (Pi.single l 1) (Pi.single k 1) := rfl
  simp only [Matrix.col_apply, starRingEnd_apply, hc]
  ring
end GroundTheory.Heights₂.Heights.ChartMongeAmpereAffineInvariance
