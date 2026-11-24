-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartMongeAmpereAffineInvariance_det_realCLE_03666fb032bf
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:09:51.328433+00:00
-- url     : https://prove2.me/submissions/99cd3308-e94c-4fba-b667-5c962ab45e53

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsSemipositiveOn
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ChartMassAffine
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartMongeAmpereAffineInvariance_realCLE_apply_c180c099b79c

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
theorem _root_.solution (P : Matrix (Fin D) (Fin D) ℂ) (hP : P.det ≠ 0) :
    LinearMap.det ((realCLE P hP : (Fin D → ℂ) →L[ℝ] (Fin D → ℂ)) : (Fin D → ℂ) →ₗ[ℝ] (Fin D → ℂ)) =
      Complex.normSq P.det := by
  have h : ((realCLE P hP : (Fin D → ℂ) →L[ℝ] (Fin D → ℂ)) : (Fin D → ℂ) →ₗ[ℝ] (Fin D → ℂ)) =
      (Matrix.toLin' P).restrictScalars ℝ := by
    ext y
    simp [realCLE_apply]
  rw [h, LinearMap.det_restrictScalars, LinearMap.det_toLin', Algebra.norm_complex_apply]
end GroundTheory.Heights₂.Heights.ChartMongeAmpereAffineInvariance
