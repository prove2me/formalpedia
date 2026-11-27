-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartDehomog_hypotheses_inhabited_7f5dbf3dd7f1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:00:55.327201+00:00
-- url     : https://prove2.me/submissions/e7602347-0b6d-4353-9ae6-80b11676b195

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_ImportsBis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Imports
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsIncidenceZeroLocus
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsChartMax
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_isProjPrime_span_X_zero_5edf23a4a896
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_linearFormLine_not_mem_span_X0_ace3f4adf1cb


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
namespace GroundTheory.Heights₂.Heights
namespace ChartDehomog
theorem _root_.solution :
    (Ideal.span {(X 0 : MvPolynomial (Fin 2) ℚ)}).IsPrime ∧
      IsHomogIdeal (Ideal.span {(X 0 : MvPolynomial (Fin 2) ℚ)}) ∧
      linForm tLine ∉ Ideal.span {(X 0 : MvPolynomial (Fin 2) ℚ)} ∧
      (X 0 : MvPolynomial (Fin 2) ℚ).IsHomogeneous 1 ∧
      (X 0 : MvPolynomial (Fin 2) ℚ) ∈
        Ideal.span {(X 0 : MvPolynomial (Fin 2) ℚ)} ⊔ Ideal.span {linForm tLine - 1} :=
  ⟨(isProjPrime_span_X_zero ℚ).isPrime, (isProjPrime_span_X_zero ℚ).isHomog, linearFormLine_not_mem_span_X0,
    isHomogeneous_X _ _, Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)⟩
end ChartDehomog
end GroundTheory.Heights₂.Heights
