-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartEnergyInvariance_maDensity_comp_affine_family_a2bd3164b5d2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:06:14.20872+00:00
-- url     : https://prove2.me/submissions/6483edef-8dcd-434b-a09a-e14dbb6da52d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartEnergyInvariant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartEnergySwap
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ChartMassAffine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartMassInvariant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartEnergyInvariant
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
open scoped ComplexOrder
noncomputable section
open GroundTheory.Heights₂.Heights.ChartEnergyInvariance
open ChartMongeAmpereAffineInvariance
variable {e : ℕ}
namespace GroundTheory.Heights₂.Heights.ChartEnergyInvariance
theorem _root_.solution {D : ℕ} (φ : Fin D → (Fin D → ℂ) → ℝ) (c : Fin D → ℂ)
    (P : Matrix (Fin D) (Fin D) ℂ) (hP : P.det ≠ 0) (κ : ℝ) (z : Fin D → ℂ) :
    maDensity (fun j => fun y => φ j (c + P *ᵥ y) + κ) z =
      Complex.normSq P.det * maDensity φ (c + P *ᵥ z) := by
  have hQ : (P.map (starRingEnd ℂ)).det = starRingEnd ℂ P.det := (RingHom.map_det (starRingEnd ℂ) P).symm
  have hH : ∀ j, cxHessian (fun y => φ j (c + P *ᵥ y) + κ) z =
      Pᵀ * cxHessian (φ j) (c + P *ᵥ z) * P.map (starRingEnd ℂ) := fun j =>
    cxHessian_comp_affine (φ j) c P hP κ z
  simp only [maDensity, hH]
  rw [mixedDisc_mul_mul (Pᵀ) (P.map (starRingEnd ℂ)) (fun j => cxHessian (φ j) (c + P *ᵥ z)), det_transpose, hQ,
    Complex.mul_conj, Complex.re_ofReal_mul]
  ring
end GroundTheory.Heights₂.Heights.ChartEnergyInvariance
