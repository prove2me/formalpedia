-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_specFirst_tLine_not_mem_ccadebe4d4f7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:55:53.266084+00:00
-- url     : https://prove2.me/submissions/1dab2b7e-f74d-4e42-8a39-55c54f140112

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LineInhabitant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsSectionOrder
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_not_dvd_specFirst_tLine_f8a08b7c59b2

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
open LineChowForm
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution :
    specFirst (D2 : MvPolynomial (Fin (1 + 1) × Fin 2) ℚ) tLine ∉ Ideal.span {qLine} := by
  rw [Ideal.mem_span_singleton]
  exact not_dvd_specFirst_tLine
end GroundTheory.Heights₂.Heights
