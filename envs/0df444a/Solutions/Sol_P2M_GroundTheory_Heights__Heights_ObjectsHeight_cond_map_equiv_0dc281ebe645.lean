-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ObjectsHeight_cond_map_equiv_0dc281ebe645
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:00:42.521813+00:00
-- url     : https://prove2.me/submissions/f7c13426-1633-4d2f-a1a3-e7fe881abb6b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SpecFirstDetFormNeZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_GaussNormEqCoeffGaussNorm

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
namespace GroundTheory.Heights₂.Heights.ObjectsHeight
theorem _root_.solution {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] (e : α ≃ᵐ β)
    (μ : Measure α) (s : Set β) : (cond μ (e ⁻¹' s)).map e = cond (μ.map e) s := by
  rw [ProbabilityTheory.cond, ProbabilityTheory.cond, Measure.map_smul, ← e.restrict_map,
    e.map_apply]
end GroundTheory.Heights₂.Heights.ObjectsHeight
