-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartMongeAmpereAffineInvariance_fderiv_fderiv_comp_affine_7e54354380f4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:29:35.397789+00:00
-- url     : https://prove2.me/submissions/0cb935b6-0796-4328-9ab0-dc33a7e5b984

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsSemipositiveOn
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ChartMassAffine

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
theorem _root_.solution (φ : (Fin D → ℂ) → ℝ) (c : Fin D → ℂ) (L : (Fin D → ℂ) ≃L[ℝ] (Fin D → ℂ))
    (κ : ℝ) (z u v : Fin D → ℂ) :
    fderiv ℝ (fderiv ℝ fun y => φ (c + L y) + κ) z u v = fderiv ℝ (fderiv ℝ φ) (c + L z) (L u) (L v) := by
  have h1 : (fderiv ℝ fun y => φ (c + L y) + κ) =
      fun y => (fderiv ℝ φ (c + L y)).comp (L : (Fin D → ℂ) →L[ℝ] (Fin D → ℂ)) := by
    funext y
    rw [fderiv_add_const]
    have : (fun y => φ (c + L y)) = (fun w => φ (c + w)) ∘ L := rfl
    rw [this, L.comp_right_fderiv, fderiv_comp_add_left]
  have h2 : (fun y => (fderiv ℝ φ (c + L y)).comp (L : (Fin D → ℂ) →L[ℝ] (Fin D → ℂ))) =
      (L.symm.arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ)) ∘ ((fun w => fderiv ℝ φ (c + w)) ∘ L) := by
    funext y
    ext w
    simp [ContinuousLinearEquiv.arrowCongr_apply]
  rw [h1, h2, ContinuousLinearEquiv.comp_fderiv, L.comp_right_fderiv, fderiv_comp_add_left]
  simp [ContinuousLinearEquiv.arrowCongr_apply]
end GroundTheory.Heights₂.Heights.ChartMongeAmpereAffineInvariance
