-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SectionLine_linearFormX1_ne_zero_7f7180d46aac
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:28:49.760144+00:00
-- url     : https://prove2.me/submissions/b67a4a15-5b1c-4bce-b416-12e59bdfeff6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsSectionOrder
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SectionLineAnyField
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SectionLine_linearForm_coeffX1_cac9564c5601

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
theorem _root_.solution : linForm (coeffX1 F) ∉ (⊥ : Ideal (MvPolynomial (Fin 2) F)) := by
  rw [linearForm_coeffX1, Ideal.mem_bot]
  exact X_ne_zero 1
end GroundTheory.Heights₂.Heights.SectionLine
