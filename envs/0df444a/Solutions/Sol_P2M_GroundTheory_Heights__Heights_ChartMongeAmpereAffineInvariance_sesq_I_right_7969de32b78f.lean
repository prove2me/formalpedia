-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartMongeAmpereAffineInvariance_sesq_I_right_7969de32b78f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:29:37.769184+00:00
-- url     : https://prove2.me/submissions/2e8f199d-27ff-4543-81f9-cea0e3b057b9

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
variable (H : (Fin D → ℂ) →L[ℝ] (Fin D → ℂ) →L[ℝ] ℝ)
namespace GroundTheory.Heights₂.Heights.ChartMongeAmpereAffineInvariance
theorem _root_.solution (u v : Fin D → ℂ) : sesq H u (Complex.I • v) = -Complex.I * sesq H u v := by
  have h : Complex.I • Complex.I • v = -v := by rw [smul_smul, Complex.I_mul_I, neg_one_smul]
  simp only [sesq, h, map_neg]
  push_cast
  linear_combination ((H u (Complex.I • v) : ℂ) - (H (Complex.I • u) v : ℂ)) / 4 * Complex.I_sq
end GroundTheory.Heights₂.Heights.ChartMongeAmpereAffineInvariance
