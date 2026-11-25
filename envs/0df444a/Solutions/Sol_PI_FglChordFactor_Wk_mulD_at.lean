-- Prove2me | solution 1 for PI.FglChordFactor.Wk.mulD_at
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:02:10.350894+00:00
-- url     : https://prove2.me/submissions/072b0a67-a1ba-41b9-b4c9-f14199b30a54

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_FglChordFactor
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupChords_DerivativeFlog
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupChords_SubstBivariateSeriesDifferencePair
import Theorems.Thm_PI_AddIntG_Wk_mem_SerS
import Theorems.Thm_PI_AddIntG_Wk_subst_psubst
import Theorems.Thm_PI_FglChordFactor_Wk_iW_mul_D


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
theorem _root_.solution (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) {u : MvPowerSeries (Fin 2) ℂ_[p]}
    (hu : PowerSeries.HasSubst u) :
    PowerSeries.subst u (iW W wq) * PowerSeries.subst u (Dser W wq) = -u := by
  rw [← PowerSeries.coe_substAlgHom hu, ← map_mul, iW_mul_D, map_neg, PowerSeries.coe_substAlgHom,
    PowerSeries.subst_X hu]
end PI.FglChordFactor.Wk
