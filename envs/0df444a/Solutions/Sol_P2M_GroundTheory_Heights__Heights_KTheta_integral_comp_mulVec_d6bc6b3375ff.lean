-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_KTheta_integral_comp_mulVec_d6bc6b3375ff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:01:34.337534+00:00
-- url     : https://prove2.me/submissions/98af506f-810c-49c0-b8fa-095822617dca

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KernelsMatrix
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_NormInvSmulMemSphere
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ThetaGauss

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open Matrix MeasureTheory Real
open scoped MatrixOrder
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.KTheta
noncomputable section
variable {g : ℕ}
namespace GroundTheory.Heights₂.Heights.KTheta
theorem _root_.solution (B : Matrix (Fin g) (Fin g) ℝ) (hB : B.det ≠ 0)
    (f : (Fin g → ℝ) → ℝ) (hf : Continuous f) :
    ∫ v, f (B *ᵥ v) = |B.det|⁻¹ * ∫ x, f x := by
  have hdet : LinearMap.det (Matrix.toLin' B) ≠ 0 := by rwa [LinearMap.det_toLin']
  have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar
    (μ := (volume : Measure (Fin g → ℝ))) hdet
  have hm : Measurable (Matrix.toLin' B) :=
    (LinearMap.continuous_of_finiteDimensional (Matrix.toLin' B)).measurable
  have h1 : ∫ v, f (B *ᵥ v) = ∫ x, f x ∂(Measure.map (Matrix.toLin' B) volume) := by
    rw [integral_map hm.aemeasurable hf.aestronglyMeasurable]
    rfl
  rw [h1, hmap, integral_smul_measure, LinearMap.det_toLin']
  rw [ENNReal.toReal_ofReal (abs_nonneg _), abs_inv, smul_eq_mul]
end GroundTheory.Heights₂.Heights.KTheta
