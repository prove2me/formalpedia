-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartIncDomain_hypotheses_inhabited_e95ae90c984c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:33:38.601119+00:00
-- url     : https://prove2.me/submissions/ff79f3bd-49a7-4370-8f51-c759b1fac240

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsSectionOrder
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_ImportsBis
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LineChowForm_isProjPrime_line_6c88d2fbf567
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_linForm_tLine_not_mem_bot_4c07bc61bfd4


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
namespace ChartIncDomain
theorem _root_.solution :
    IsProjPrime (⊥ : Ideal (MvPolynomial (Fin 2) ℚ)) ∧ linForm tLine ∉ (⊥ : Ideal (MvPolynomial (Fin 2) ℚ)) :=
  ⟨LineChowForm.isProjPrime_line, linForm_tLine_not_mem_bot⟩
end ChartIncDomain
end GroundTheory.Heights₂.Heights
