-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartEnergySwapHessian_sesq_eq_of_form_c6b7ddfb0652
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:36:46.753448+00:00
-- url     : https://prove2.me/submissions/db0b418b-56ff-429c-82b8-ab073e499d4e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ChartMassAffine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ChartHessHolo

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
open ReciprocityTheory.ChartRestriction.G.Geo Matrix Filter Topology
noncomputable section
open GroundTheory.Heights₂.Heights.ChartEnergySwapHessian
open ChartMongeAmpereAffineInvariance
variable {D : ℕ} {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E'] [NormedSpace ℝ E']
  [IsScalarTower ℝ ℂ E']
namespace GroundTheory.Heights₂.Heights.ChartEnergySwapHessian
theorem _root_.solution (H H₀ : (Fin D → ℂ) →L[ℝ] (Fin D → ℂ) →L[ℝ] ℝ)
    (L : (Fin D → ℂ) →L[ℂ] (Fin D → ℂ)) (R : (Fin D → ℂ) → (Fin D → ℂ) → ℝ)
    (hH : ∀ u v, H u v = H₀ (L u) (L v) + R u v)
    (hR₁ : ∀ u v, R (Complex.I • u) (Complex.I • v) = -R u v)
    (hR₂ : ∀ u v, R u (Complex.I • v) = R (Complex.I • u) v) (a b : Fin D → ℂ) :
    sesq H a b = sesq H₀ (L a) (L b) := by
  simp only [sesq, hH, map_smul]
  rw [hR₁, hR₂]
  push_cast
  ring
end GroundTheory.Heights₂.Heights.ChartEnergySwapHessian
