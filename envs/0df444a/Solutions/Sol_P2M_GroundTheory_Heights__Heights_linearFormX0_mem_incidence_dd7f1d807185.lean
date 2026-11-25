-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_linearFormX0_mem_incidence_dd7f1d807185
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:40:55.176675+00:00
-- url     : https://prove2.me/submissions/27815772-b6fd-448f-a686-7c0c42f6adb2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LowerBoundConditional
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsIncidenceZeroLocus

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
open MvPolynomial
noncomputable section
attribute [local instance] MvPolynomial.gradedAlgebra
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution :
    linearFormX0 (AlgebraicClosure ℚ) ∈ incidence (Ideal.span {(X 0 : MvPolynomial (Fin 2) ℚ)}) 1 := by
  refine ⟨![0, 1], fun h => one_ne_zero (congrFun h 1), fun g hg => ?_, fun i => ?_⟩
  · obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hg
    simp
  · simp [linearFormX0]
end GroundTheory.Heights₂.Heights
