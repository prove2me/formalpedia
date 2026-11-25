-- Prove2me | solution 1 for PI.FglChordFactor.Wk.negsub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:25:33.362012+00:00
-- url     : https://prove2.me/submissions/3bf61442-1c1d-47ec-bf15-3fde1d6ed769

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_FglChordFactor
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupChords_DerivativeFlog
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupChords_SubstBivariateSeriesDifferencePair
import Theorems.Thm_PI_AddIntG_Wk_mem_SerS
import Theorems.Thm_PI_AddIntG_Wk_subst_psubst
import Theorems.Thm_PI_FglChordFactor_Wk_flog_iW
import Theorems.Thm_PI_FglChordFactor_Wk_hasSubst_iW


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical
open PI PI.FglChordFactor PI.FglChordFactor.Wk
open PI.AddIntG.Wk (SerS mem_SerS subst_psubst)
variable {p : ℕ} [Fact p.Prime]
namespace PI.FglChordFactor.Wk
theorem _root_.solution {W : WeierstrassCurve ℂ_[p]} {wq : PowerSeries ℂ_[p]} (h : IsWq W wq)
    {u : MvPowerSeries (Fin 2) ℂ_[p]} (hu : PowerSeries.HasSubst u) :
    PowerSeries.subst (PowerSeries.subst u (iW W wq)) (flog W wq) = -PowerSeries.subst u (flog W wq) := by
  rw [← PowerSeries.subst_comp_subst_apply (hasSubst_iW W wq) hu, flog_iW h,
    ← PowerSeries.coe_substAlgHom hu, map_neg]
end PI.FglChordFactor.Wk
