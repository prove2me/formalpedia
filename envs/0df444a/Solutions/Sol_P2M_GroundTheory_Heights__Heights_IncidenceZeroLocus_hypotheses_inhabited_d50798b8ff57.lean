-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IncidenceZeroLocus_hypotheses_inhabited_d50798b8ff57
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:55:48.155031+00:00
-- url     : https://prove2.me/submissions/4f35cc52-0907-4058-af1d-c220215045d9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LowerBoundConditional
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsIncidenceZeroLocus
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_isProjPrime_span_X_zero_5edf23a4a896
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_linearFormX0_mem_incidence_dd7f1d807185

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
namespace IncidenceZeroLocus
theorem _root_.solution :
    IsHomogIdeal (Ideal.span {(X 0 : MvPolynomial (Fin 2) ℚ)}) ∧
      ∀ g ∈ incIdeal (Ideal.span {(X 0 : MvPolynomial (Fin 2) ℚ)}) 1,
        aeval (linearFormX0 (AlgebraicClosure ℚ)) g = 0 := by
  refine ⟨(isProjPrime_span_X_zero ℚ).isHomog, fun g hg => ?_⟩
  simp only [incIdeal, Submodule.mem_iInf, RingHom.mem_ker] at hg
  exact hg _ linearFormX0_mem_incidence
end IncidenceZeroLocus
end GroundTheory.Heights₂.Heights
