-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartMongeAmpereAffineInvariance_smul_eq_re_add_im_4c7b8f6c23de
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:54:24.704835+00:00
-- url     : https://prove2.me/submissions/4852dfd9-f7f1-4ed4-9c81-92e70d806935

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
theorem _root_.solution (a : ℂ) (u : Fin D → ℂ) : a • u = a.re • u + a.im • (Complex.I • u) := by
  funext p
  simp only [Pi.add_apply, Pi.smul_apply, Complex.real_smul, smul_eq_mul]
  conv_lhs => rw [← Complex.re_add_im a]
  ring
end GroundTheory.Heights₂.Heights.ChartMongeAmpereAffineInvariance
