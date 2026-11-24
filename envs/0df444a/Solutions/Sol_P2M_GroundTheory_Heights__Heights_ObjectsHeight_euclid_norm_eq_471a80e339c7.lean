-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ObjectsHeight_euclid_norm_eq_471a80e339c7
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:57:32.393537+00:00
-- url     : https://prove2.me/submissions/5f210517-dabb-4f32-ae61-1ffb21d3721e

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
theorem _root_.solution (v : Fin n → ℂ) : ‖WithLp.toLp 2 v‖ = √(∑ i, ‖v i‖ ^ 2) := by
  rw [EuclideanSpace.norm_eq]
end GroundTheory.Heights₂.Heights.ObjectsHeight
