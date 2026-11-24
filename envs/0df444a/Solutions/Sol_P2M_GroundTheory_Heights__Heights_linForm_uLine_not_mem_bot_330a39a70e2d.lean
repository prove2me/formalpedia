-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_linForm_uLine_not_mem_bot_330a39a70e2d
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:54:51.10352+00:00
-- url     : https://prove2.me/submissions/ed5b6525-f9e2-46ef-8407-029952cc7eb4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LineInhabitant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsSectionOrder
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LineChowForm_linForm_line_66a12de41669


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
theorem _root_.solution : linForm uLine ∉ (⊥ : Ideal (MvPolynomial (Fin 2) ℚ)) :=
  linForm_line
end GroundTheory.Heights₂.Heights
