-- Prove2me | solution 1 for PI.GTNum.interlacing_defect_eq_card
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:05:41.56179+00:00
-- url     : https://prove2.me/submissions/fa78b019-4094-4b09-8e79-c6ab632df7f8

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_GTDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinTopCoefficient_CardEraseIccMin
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinTopCoefficient_InterlacingDefectEqCard
import Theorems.Thm_PI_GTNum_card_R_erase

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.GTNum
open Formalism.BasicNotions PI Finset
variable {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n)
namespace PI.GTNum
theorem _root_.solution (hI : Interlace h lam sg) :
    D1 h lam sg = ((∑ i : Fin n, ((Rset h lam sg i).erase (sg.w i)).card : ℕ) : ℤ) := by
  unfold D1
  push_cast
  exact Finset.sum_congr rfl (fun i _ => (card_R_erase h lam sg hI i).symm)
end PI.GTNum
