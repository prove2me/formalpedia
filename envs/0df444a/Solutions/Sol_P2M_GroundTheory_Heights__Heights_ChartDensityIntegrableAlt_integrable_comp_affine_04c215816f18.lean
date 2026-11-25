-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartDensityIntegrableAlt_integrable_comp_affine_04c215816f18
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T02:36:46.292082+00:00
-- url     : https://prove2.me/submissions/3f40aec5-d8ff-47b8-bcf0-7af5280eaea0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AMassStA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartDensityIntegrable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ChartMassAffine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartDensityIntegrable
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
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Matrix MeasureTheory Filter
open scoped ComplexOrder
noncomputable section
open GroundTheory.Heights₂.Heights.ChartDensityIntegrableAlt
namespace GroundTheory.Heights₂.Heights.ChartDensityIntegrableAlt
theorem _root_.solution {D : ℕ} {f : (Fin D → ℂ) → ℝ} (hf : Integrable f) (c : Fin D → ℂ)
    (P : Matrix (Fin D) (Fin D) ℂ) (hP : P.det ≠ 0) : Integrable (fun y => f (c + P *ᵥ y)) := by
  set L := ChartMongeAmpereAffineInvariance.realCLE P hP
  have hpos : 0 < Complex.normSq P.det := Complex.normSq_pos.mpr hP
  have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure (Fin D → ℂ))
    (f := ((L : (Fin D → ℂ) →L[ℝ] (Fin D → ℂ)) : (Fin D → ℂ) →ₗ[ℝ] (Fin D → ℂ)))
    (by rw [ChartMongeAmpereAffineInvariance.det_realCLE]; exact hpos.ne')
  have hcoe : ⇑((L : (Fin D → ℂ) →L[ℝ] (Fin D → ℂ)) : (Fin D → ℂ) →ₗ[ℝ] (Fin D → ℂ)) = ⇑L := rfl
  rw [hcoe] at hmap
  have hg : Integrable (fun w => f (c + w)) (Measure.map L volume) := by
    rw [hmap]
    exact (hf.comp_add_left c).smul_measure ENNReal.ofReal_ne_top
  exact L.toHomeomorph.measurableEmbedding.integrable_map_iff.mp hg
end GroundTheory.Heights₂.Heights.ChartDensityIntegrableAlt
