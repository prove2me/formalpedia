-- Prove2me | solution 1 for PI.JetsPhW.W.cubeDefectFormula_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:02:47.535816+00:00
-- url     : https://prove2.me/submissions/1569b869-93d6-4396-a1f5-8a6d4208c15c

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JetIntegrality_TwoUnit
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JetIntegrality_PolarizationDifferenceFormulaHolds
import Theorems.Thm_PI_JetsPhW_W_phAt_add
import Theorems.Thm_PI_JetsPhW_W_l_add
import Theorems.Thm_PI_JetsPhW_W_cc_add

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.JetsPhW PI.JetsPhW.W
open PI.JetsPhW
namespace PI.JetsPhW.W
theorem _root_.solution : Rw3 := by
  intro p _ l ex ph h
  obtain ⟨hex, hl, -⟩ := h
  have h0 : MvPowerSeries.constantCoeff (PI.JetsPhW.Xv 0 : MvPowerSeries (Fin 3) ℂ_[p]) = 0 :=
    MvPowerSeries.constantCoeff_X _
  have h1 : MvPowerSeries.constantCoeff (PI.JetsPhW.Xv 1 : MvPowerSeries (Fin 3) ℂ_[p]) = 0 :=
    MvPowerSeries.constantCoeff_X _
  have h2 : MvPowerSeries.constantCoeff (PI.JetsPhW.Xv 2 : MvPowerSeries (Fin 3) ℂ_[p]) = 0 :=
    MvPowerSeries.constantCoeff_X _
  unfold PI.JetsPhW.cubeE
  rw [phAt_add hex hl (cc_add hex hl h0 h1) h2,
    l_add hex hl h0 h1, phAt_add hex hl h0 h1,
    phAt_add hex hl h1 h2, phAt_add hex hl h2 h0]
end PI.JetsPhW.W
