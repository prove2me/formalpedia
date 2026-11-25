-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ObjectsHeight_volume_normSq_eq_one_e3f936075ac2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:45:27.854807+00:00
-- url     : https://prove2.me/submissions/088953d1-d766-4ad3-bc99-e121f7da39a4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SpecFirstDetFormNeZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_GaussNormEqCoeffGaussNorm
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsHeight_euclid_norm_eq_471a80e339c7

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
open MvPolynomial MeasureTheory NumberField Matrix ProbabilityTheory
noncomputable section
open GroundTheory.Heights₂.Heights.ObjectsHeight
variable {n : ℕ}
variable {k : ℕ}
namespace GroundTheory.Heights₂.Heights.ObjectsHeight
theorem _root_.solution :
    (volume : Measure (Fin n → ℂ)) {v | IndefiniteRowSideFullHecke.ArithBezout.normSq v = 1} = 0 := by
  rcases n with _ | m
  · have : {v : Fin 0 → ℂ | IndefiniteRowSideFullHecke.ArithBezout.normSq v = 1} = ∅ := by
      ext v
      simp [IndefiniteRowSideFullHecke.ArithBezout.normSq]
    rw [this, measure_empty]
  · let e : (Fin (m + 1) → ℂ) ≃L[ℝ] EuclideanSpace ℂ (Fin (m + 1)) :=
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (m + 1) => ℂ)).symm
    have : (volume.map e).IsAddHaarMeasure := e.isAddHaarMeasure_map _
    have hset : {v : Fin (m + 1) → ℂ | IndefiniteRowSideFullHecke.ArithBezout.normSq v = 1} =
        e ⁻¹' Metric.sphere 0 1 := by
      ext v
      simp only [Set.mem_ofPred_eq, Set.mem_preimage, mem_sphere_zero_iff_norm]
      have : ‖e v‖ = √(IndefiniteRowSideFullHecke.ArithBezout.normSq v) := by
        show ‖WithLp.toLp 2 v‖ = _
        rw [euclid_norm_eq]
        rfl
      rw [this, Real.sqrt_eq_one]
    rw [hset, ← Measure.map_apply e.continuous.measurable Metric.isClosed_sphere.measurableSet]
    exact Measure.addHaar_sphere _ 0 1
end GroundTheory.Heights₂.Heights.ObjectsHeight
