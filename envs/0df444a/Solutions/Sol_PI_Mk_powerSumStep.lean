-- Prove2me | solution 1 for PI.Mk.powerSumStep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:09:34.163437+00:00
-- url     : https://prove2.me/submissions/74883544-c340-4023-9599-1570593440ad

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinkowskiBound_PowerSumStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinkowskiBound_PowerSum
import Theorems.Thm_PI_Mk_card_dvd_sum_trace
import Theorems.Thm_PI_Mk_kron_mul
import Theorems.Thm_PI_Mk_trace_kron

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.Mk
open Matrix Finset
namespace PI.Mk
theorem _root_.solution : PowerSumStep := by
  intro N P _ k
  have h := card_dvd_sum_trace (H := P)
    (fun g => kron k (((g : Matrix.GeneralLinearGroup (Fin N) ℤ)) : Matrix (Fin N) (Fin N) ℤ))
    (fun a b => by simp only [Subgroup.coe_mul, Units.val_mul, kron_mul])
  simpa only [trace_kron] using h
end PI.Mk
