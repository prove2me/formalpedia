-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartMongeAmpereAffineInvariance_integral_comp_affine_bae7cf364846
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:21:39.055419+00:00
-- url     : https://prove2.me/submissions/a7617e81-b016-4077-b654-8123877d568f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsSemipositiveOn
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ChartMassAffine
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartMongeAmpereAffineInvariance_det_realCLE_03666fb032bf

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
theorem _root_.solution (f : (Fin D → ℂ) → ℝ) (c : Fin D → ℂ) (P : Matrix (Fin D) (Fin D) ℂ)
    (hP : P.det ≠ 0) :
    ∫ y, f (c + P *ᵥ y) = (Complex.normSq P.det)⁻¹ * ∫ y, f y := by
  set L := realCLE P hP
  have hpos : 0 < Complex.normSq P.det := Complex.normSq_pos.mpr hP
  have hdet := det_realCLE P hP
  have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure (Fin D → ℂ))
    (f := ((L : (Fin D → ℂ) →L[ℝ] (Fin D → ℂ)) : (Fin D → ℂ) →ₗ[ℝ] (Fin D → ℂ))) (by rw [hdet]; exact hpos.ne')
  have hcoe : ⇑((L : (Fin D → ℂ) →L[ℝ] (Fin D → ℂ)) : (Fin D → ℂ) →ₗ[ℝ] (Fin D → ℂ)) = ⇑L := rfl
  rw [hcoe, hdet] at hmap
  calc ∫ y, f (c + P *ᵥ y) = ∫ y, (fun w => f (c + w)) (L y) := rfl
    _ = ∫ w, f (c + w) ∂(Measure.map L volume) :=
        (L.toHomeomorph.measurableEmbedding.integral_map (fun w => f (c + w))).symm
    _ = (Complex.normSq P.det)⁻¹ * ∫ y, f y := by
        rw [hmap, integral_smul_measure, integral_add_left_eq_self, ENNReal.toReal_ofReal (abs_nonneg _),
          abs_inv, abs_of_pos hpos, smul_eq_mul]
end GroundTheory.Heights₂.Heights.ChartMongeAmpereAffineInvariance
