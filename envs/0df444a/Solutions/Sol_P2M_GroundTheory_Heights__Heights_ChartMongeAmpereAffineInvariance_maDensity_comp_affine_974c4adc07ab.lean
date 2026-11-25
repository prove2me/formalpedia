-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartMongeAmpereAffineInvariance_maDensity_comp_affine_974c4adc07ab
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T06:13:43.855333+00:00
-- url     : https://prove2.me/submissions/40dc7cbb-0077-4756-a47e-0afae4b4834b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsSemipositiveOn
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ChartMassAffine
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartMongeAmpereAffineInvariance_cxHessian_comp_affine_e54c44d4644c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartMongeAmpereAffineInvariance_mixedDisc_mul_mul_6e0de3118a6e

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
    maDensity (fun _ : Fin D => fun y => φ (c + P *ᵥ y) + κ) z =
      Complex.normSq P.det * maDensity (fun _ : Fin D => φ) (c + P *ᵥ z) := by
  have hQ : (P.map (starRingEnd ℂ)).det = starRingEnd ℂ P.det := (RingHom.map_det (starRingEnd ℂ) P).symm
  simp only [maDensity, cxHessian_comp_affine φ c P hP κ z]
  rw [mixedDisc_mul_mul (Pᵀ) (P.map (starRingEnd ℂ)) (fun _ => cxHessian φ (c + P *ᵥ z)), det_transpose, hQ,
    Complex.mul_conj, Complex.re_ofReal_mul]
  ring
end GroundTheory.Heights₂.Heights.ChartMongeAmpereAffineInvariance
