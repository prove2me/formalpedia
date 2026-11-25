-- Prove2me | solution 1 for PI.OddDualWeyl.columnSpanDual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:05:24.203265+00:00
-- url     : https://prove2.me/submissions/4a100b5a-2380-457c-b864-8a5b2f85cbcf

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacRev
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_ExistsEqMulOfColumnSpanLe
import Theorems.Thm_PI_OddDualWeyl_Misc_exists_eq_mul_of_columnSpan_le
import Theorems.Thm_PI_OddDualWeyl_Misc_colSpan_mul_le
import Theorems.Thm_PI_OddDualWeyl_Misc_invT_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Matrix
noncomputable section
open PI PI.OddDualWeyl
namespace PI.OddDualWeyl
theorem _root_.solution : DualB := by
  intro O K _ _ _ m g g' hg hg' h
  obtain ⟨v, hv⟩ := PI.OddDualWeyl.Misc.exists_eq_mul_of_columnSpan_le (O := O) g' g h.ge
  obtain ⟨w, hw⟩ := PI.OddDualWeyl.Misc.exists_eq_mul_of_columnSpan_le (O := O) g g' h.le
  apply le_antisymm
  · rw [PI.OddDualWeyl.Misc.invT_eq hg hg' v hv]
    exact PI.OddDualWeyl.Misc.colSpan_mul_le _ _
  · rw [PI.OddDualWeyl.Misc.invT_eq hg' hg w hw]
    exact PI.OddDualWeyl.Misc.colSpan_mul_le _ _
end PI.OddDualWeyl
