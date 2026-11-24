-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ObjectsHeight_continuous_formNorm_9c335fffca42
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:00:43.530639+00:00
-- url     : https://prove2.me/submissions/24d7b60f-b2b3-4e62-8be6-d5d16e7f758f

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
variable {k : ℕ}
namespace GroundTheory.Heights₂.Heights.ObjectsHeight
theorem _root_.solution (S : Matrix (Fin n) (Fin n) ℂ) :
    Continuous (IndefiniteRowSideFullHecke.ArithBezout.formNorm S) := by
  unfold IndefiniteRowSideFullHecke.ArithBezout.formNorm
  exact continuous_norm.comp ((PiLp.continuous_toLp 2 _).comp
    (Continuous.matrix_mulVec continuous_const continuous_id))
end GroundTheory.Heights₂.Heights.ObjectsHeight
