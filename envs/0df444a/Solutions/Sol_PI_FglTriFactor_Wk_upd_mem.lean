-- Prove2me | solution 1 for PI.FglTriFactor.Wk.upd_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:39:59.894695+00:00
-- url     : https://prove2.me/submissions/e0418486-bea0-4bdb-8898-adc8e52f7c2f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_SubstMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupTriangles_CoeffSubstUpdZero
import Theorems.Thm_PI_FglTriFactor_Wk_upd_self
import Theorems.Thm_PI_FglTriFactor_Wk_upd_ne
import Theorems.Thm_P2M_PI_FglTriFactor_Wk_X_mem_SerS__cfa52566366e
import Theorems.Thm_PI_AddIntG_Wk_mem_SerS
import Theorems.Thm_PI_AddIntG_Wk_mvsubst_mem_SerS


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.FglTriFactor PI.FglTriFactor.Wk
open PI.AddIntG.Wk (SerS mem_SerS mvsubst_mem_SerS)
variable {K : Type*} [Field K] {σ : Type*} [Finite σ] [DecidableEq σ]
namespace PI.FglTriFactor.Wk
theorem _root_.solution {S : Subring K} (k : σ) {t : MvPowerSeries σ K} (ht : t ∈ SerS S σ) (i : σ) :
    upd k t i ∈ SerS S σ := by
  rcases eq_or_ne i k with rfl | h
  · rw [upd_self]; exact ht
  · rw [upd_ne t h]; exact X_mem_SerS' S i
end PI.FglTriFactor.Wk
