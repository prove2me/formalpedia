-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_linForm_tLine_1098a18ec0be
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:52:35.82427+00:00
-- url     : https://prove2.me/submissions/43f04ebf-cf89-4d56-bb22-87d39dd4be7b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LineInhabitant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsSectionOrder

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
theorem _root_.solution : linForm tLine = (X 1 : MvPolynomial (Fin 2) ℚ) := by
  simp [linForm, tLine, Fin.sum_univ_two]
end GroundTheory.Heights₂.Heights
