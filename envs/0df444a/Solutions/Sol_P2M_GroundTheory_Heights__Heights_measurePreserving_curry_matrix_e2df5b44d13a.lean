-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_measurePreserving_curry_matrix_e2df5b44d13a
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:04:39.926841+00:00
-- url     : https://prove2.me/submissions/77759aa4-dd06-40b9-a9fc-2a8f48e03ad5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeFibreAverage
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeIntegralMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntPoly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PPointLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeMassOfFibre

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
open MvPolynomial MeasureTheory Module
open scoped ENNReal
noncomputable section
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (m n : ℕ) :
    MeasurePreserving (MeasurableEquiv.curry (Fin m) (Fin n) ℂ)
      (volume : Measure (Fin m × Fin n → ℂ)) (Measure.pi fun _ : Fin m => (volume : Measure (Fin n → ℂ))) := by
  refine ⟨(MeasurableEquiv.curry _ _ _).measurable, ?_⟩
  rw [MeasurableEquiv.map_apply_eq_iff_map_symm_apply_eq]
  show Measure.pi (fun _ : Fin m × Fin n => (volume : Measure ℂ)) = _
  refine Measure.pi_eq fun s hs => ?_
  rw [MeasurableEquiv.map_apply, MeasurableEquiv.coe_curry_symm]
  have hset : Function.uncurry ⁻¹' Set.univ.pi s =
      Set.univ.pi fun i : Fin m => Set.univ.pi fun j : Fin n => s (i, j) := by
    ext x
    simp
  rw [hset, Measure.pi_pi]
  simp_rw [volume_pi, Measure.pi_pi]
  rw [Fintype.prod_prod_type]
end GroundTheory.Heights₂.Heights
