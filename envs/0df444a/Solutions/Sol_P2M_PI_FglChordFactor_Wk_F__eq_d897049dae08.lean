-- Prove2me | solution 1 for P2M_PI_FglChordFactor_Wk_F__eq_d897049dae08
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:32:46.656414+00:00
-- url     : https://prove2.me/submissions/48d9f0cf-63e0-451c-8e39-796cc05309bc

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_FglChordFactor
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupChords_DerivativeFlog
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupChords_SubstBivariateSeriesDifferencePair
import Theorems.Thm_PI_FglChordFactor_Wk_subst_pair_formal_add
import Theorems.Thm_PI_FglChordFactor_Wk_negsub
import Theorems.Thm_PI_FglChordFactor_Wk_constantCoeff_inverse_variable
import Theorems.Thm_PI_AddIntG_Wk_mem_SerS
import Theorems.Thm_PI_AddIntG_Wk_subst_psubst
import Theorems.Thm_PI_FglChordFactor_Wk_flog_const
import Theorems.Thm_PI_FglChordFactor_Wk_hasSubst2


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
theorem _root_.solution {W : WeierstrassCurve ℂ_[p]} {wq ex : PowerSeries ℂ_[p]} (hW : IsWq W wq) :
    sub (flog W wq) ex (MvPowerSeries.X 0) (MvPowerSeries.X 1) =
      MvPowerSeries.subst ![MvPowerSeries.X 0,
        PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[p]) (iW W wq)]
        (add (flog W wq) ex (MvPowerSeries.X 0) (MvPowerSeries.X 1)) := by
  rw [subst_pair_formal_add (flog_const W wq) (hasSubst2 (MvPowerSeries.constantCoeff_X 0) (constantCoeff_inverse_variable W wq 1))]
  simp only [PI.FglChordFactor.add, PI.FglChordFactor.sub, PI.FglChordFactor.pt, PI.FglChordFactor.lg]
  rw [negsub hW (PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X 1 : MvPowerSeries.constantCoeff (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[p]) = 0)), sub_eq_add_neg]
end PI.FglChordFactor.Wk
