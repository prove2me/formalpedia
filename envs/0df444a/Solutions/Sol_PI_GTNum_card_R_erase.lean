-- Prove2me | solution 1 for PI.GTNum.card_R_erase
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:59:25.39115+00:00
-- url     : https://prove2.me/submissions/e860f40e-526c-4a1f-a5f0-f2cbbb3833f4

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_GTDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinTopCoefficient_CardEraseIccMin
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinTopCoefficient_InterlacingDefectEqCard
import Theorems.Thm_PI_GTNum_determinantWeight_nonneg
import Theorems.Thm_PI_GTNum_sg_mem_R
import Theorems.Thm_PI_GTNum_lam_succ_le
import Theorems.Thm_PI_GTNum_card_erase_Icc_min


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
theorem _root_.solution (hI : Interlace h lam sg) (i : Fin n) :
    ((((Rset h lam sg i).erase (sg.w i)).card : ℕ) : ℤ) =
      min (lam.w ⟨i.1, by omega⟩ - lam.w ⟨i.1 + 1, by omega⟩) (D0 h lam sg) := by
  have hm := sg_mem_R h lam sg hI i
  unfold Rset at hm ⊢
  exact card_erase_Icc_min _ _ _ _ (lam_succ_le h lam i) (determinantWeight_nonneg h lam sg hI) hm
end PI.GTNum
