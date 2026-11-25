-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_specialize_det_lineForm_eq_a195f3e197c2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:40:36.194633+00:00
-- url     : https://prove2.me/submissions/b55cfc3d-b4a3-4bf0-ac4b-024c42340b76

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
theorem _root_.solution :
    specFirst (D2 : MvPolynomial (Fin (1 + 1) × Fin 2) ℚ) tLine = -X (0, 0) := by
  simp [specFirst, D2, specFirstVar, tLine]
  rfl
end GroundTheory.Heights₂.Heights
