-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SectionLine_linearForm_coeffX1_cac9564c5601
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:15:56.380802+00:00
-- url     : https://prove2.me/submissions/bae4b04f-15a3-4318-b6b3-bb35704892e9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsSectionOrder
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SectionLineAnyField

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
open MvPolynomial LineChowForm
noncomputable section
open GroundTheory.Heights₂.Heights.SectionLine
variable (F : Type) [Field F]
namespace GroundTheory.Heights₂.Heights.SectionLine
theorem _root_.solution : linForm (coeffX1 F) = (X 1 : MvPolynomial (Fin 2) F) := by
  simp [linForm, coeffX1, Fin.sum_univ_two]
end GroundTheory.Heights₂.Heights.SectionLine
