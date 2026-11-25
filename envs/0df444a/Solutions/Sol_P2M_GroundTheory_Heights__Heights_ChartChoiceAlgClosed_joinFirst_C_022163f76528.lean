-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartChoiceAlgClosed_joinFirst_C_022163f76528
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:36:46.477637+00:00
-- url     : https://prove2.me/submissions/9322faa7-7a14-4c51-a442-654b81ee96ea

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsChartChoiceAlgClosed
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PChartChoiceAlgClosed

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
open GroundTheory.Heights₂.Heights.ChartChoiceAlgClosed
variable {F : Type} [Field F] {n e : ℕ}
namespace GroundTheory.Heights₂.Heights.ChartChoiceAlgClosed
theorem _root_.solution (a : MvPolynomial (Fin e × Fin n) F) :
    joinFirst F e n (C a) = rename (shiftVar e n) a := by
  simp [joinFirst]
end GroundTheory.Heights₂.Heights.ChartChoiceAlgClosed
