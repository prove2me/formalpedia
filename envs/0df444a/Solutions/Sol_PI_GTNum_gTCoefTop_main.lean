-- Prove2me | solution 1 for PI.GTNum.gTCoefTop_main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:21:24.645072+00:00
-- url     : https://prove2.me/submissions/952a6720-8859-4c4b-b314-9182f6fba1e8

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_GTCoefTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinTopCoefficient_CardEraseIccMin
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinTopCoefficient_InterlacingDefectEqCard
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinTopCoefficient_GTCoefTopMain
import Theorems.Thm_PI_GTNum_abs_cBr_le
import Theorems.Thm_PI_GTNum_top_indep
import Theorems.Thm_PI_GTNum_interlacing_defect_eq_card


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
namespace PI.GTNum
theorem _root_.solution : PI.GTCoefTop := by
  intro n N h hn lam sg hI htop
  refine ⟨?_, fun lam' hag htop' => top_indep h hn lam lam' sg hag htop htop'⟩
  set K : ℕ := ∑ i : Fin n, ((Rset h lam sg i).erase (sg.w i)).card with hK
  have hD1 : (n : ℤ) * D1 h lam sg = ((n * K : ℕ) : ℤ) := by
    rw [interlacing_defect_eq_card h lam sg hI, ← hK, Nat.cast_mul]
  have hb := abs_cBr_le h hn lam sg hI
  rw [hD1, Int.cast_natCast, Real.rpow_natCast, ← Int.cast_abs]
  exact_mod_cast hb
end PI.GTNum
