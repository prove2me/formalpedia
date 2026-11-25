-- Prove2me | solution 1 for PI.Dv.TIW.volume_sum_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:15:31.916106+00:00
-- url     : https://prove2.me/submissions/0467cc16-f67a-4eaf-806c-3e8feb274959

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_DvTransferIdxOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_FinsumEqLogNorm
import Theorems.Thm_PI_Dv_TIW_finsum_eq_log_norm
import Theorems.Thm_PI_Dv_TIW_abs_norm_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.TIW
open Formalism.BasicNotions NumberField IsDedekindDomain
open scoped WithZero
namespace PI.Dv.TIW
theorem _root_.solution : VSumLe := by
  intro K _ _ x B hx hB hσ
  rw [finsum_eq_log_norm x hx]
  have hd : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  have hN : (0 : ℝ) < |((Algebra.norm ℤ x : ℤ) : ℝ)| := by
    rw [abs_pos, Int.cast_ne_zero, Ne, Algebra.norm_eq_zero_iff]
    exact hx
  rw [div_le_iff₀ hd, mul_comm, ← Real.log_pow]
  exact Real.log_le_log hN (abs_norm_le x B hB.le hσ)
end PI.Dv.TIW
