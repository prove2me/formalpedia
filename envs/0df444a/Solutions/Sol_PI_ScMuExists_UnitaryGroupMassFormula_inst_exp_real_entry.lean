-- Prove2me | solution 1 for PI.ScMuExists.UnitaryGroupMassFormula.inst_exp_real_entry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:28:40.795905+00:00
-- url     : https://prove2.me/submissions/4e494365-1154-4f41-8cec-6ba463c7e491

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_InstDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_InstExp
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open Matrix
open PI PI.ScMuExists PI.ScMuExists.UnitaryGroupMassFormula
namespace PI.ScMuExists.UnitaryGroupMassFormula
theorem _root_.solution (l : ℝ) (y : ℂ) :
    NormedSpace.exp (l : ℂ) * y = y ↔ (l : ℂ) * y = 0 := by
  have hE : NormedSpace.exp (l : ℂ) = ((Real.exp l : ℝ) : ℂ) := by
    rw [Complex.ofReal_exp]
    first
      | rw [Complex.exp_eq_exp_ℂ]
      | exact (congrFun Complex.exp_eq_exp_ℂ (l : ℂ)).symm
  rw [hE]
  constructor
  · intro h
    by_cases hy : y = 0
    · simp [hy]
    · have h1 : ((Real.exp l : ℝ) : ℂ) = 1 := mul_right_cancel₀ hy (h.trans (one_mul y).symm)
      have h2 : Real.exp l = 1 := by exact_mod_cast h1
      have h3 : l = 0 := Real.exp_eq_one_iff l |>.mp h2
      simp [h3]
  · intro h
    rcases mul_eq_zero.mp h with hl | hy
    · have h3 : l = 0 := by exact_mod_cast hl
      simp [h3]
    · simp [hy]
end PI.ScMuExists.UnitaryGroupMassFormula
