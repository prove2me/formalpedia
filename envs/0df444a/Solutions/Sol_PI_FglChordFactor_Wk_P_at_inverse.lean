-- Prove2me | solution 1 for PI.FglChordFactor.Wk.P_at_inverse
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:15:15.301268+00:00
-- url     : https://prove2.me/submissions/3b0343bf-b756-4531-aba7-dda8348e3ae0

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_FglChordFactor
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupChords_DerivativeFlog
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupChords_SubstBivariateSeriesDifferencePair
import Theorems.Thm_PI_FglChordFactor_Wk_mulD_at
import Theorems.Thm_PI_FglChordFactor_Wk_constantCoeff_inverse_variable
import Theorems.Thm_PI_AddIntG_Wk_mem_SerS
import Theorems.Thm_PI_AddIntG_Wk_subst_psubst
import Theorems.Thm_PI_FglChordFactor_Wk_hasSubst2
import Theorems.Thm_PI_FglChordFactor_Wk_hasSubst_iW
import Theorems.Thm_PI_FglChordFactor_Wk_subst_pair_first_series
import Theorems.Thm_PI_FglChordFactor_Wk_subst_pair_first_variable
import Theorems.Thm_PI_FglChordFactor_Wk_subst_pair_second_series
import Theorems.Thm_PI_FglChordFactor_Wk_subst_pair_second_variable
import Theorems.Thm_PI_FglChordFactor_Wk_wq_iW


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
theorem _root_.solution {W : WeierstrassCurve ℂ_[p]} {wq : PowerSeries ℂ_[p]} (hW : IsWq W wq) :
    MvPowerSeries.subst ![MvPowerSeries.X 0,
      PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[p]) (iW W wq)] (Pser wq) = 0 := by
  have hX0 : PowerSeries.HasSubst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[p]) := PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X 0 : MvPowerSeries.constantCoeff (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[p]) = 0)
  have hs := hasSubst2 (MvPowerSeries.constantCoeff_X 0) (constantCoeff_inverse_variable W wq 0)
  have hm := mulD_at W wq hX0
  have key : ∀ a i d w : MvPowerSeries (Fin 2) ℂ_[p], i * d = -a → a ^ 2 * w - i ^ 2 * (w * d ^ 2) = 0 := by
    intro a i d w h
    linear_combination (-(i * d - a) * w) * h
  unfold Pser
  rw [← MvPowerSeries.coe_substAlgHom hs, map_sub, map_mul, map_mul, map_pow, map_pow,
    MvPowerSeries.coe_substAlgHom, subst_pair_first_variable hs, subst_pair_second_variable hs, subst_pair_first_series hs, subst_pair_second_series hs,
    ← PowerSeries.subst_comp_subst_apply (hasSubst_iW W wq) hX0, wq_iW hW,
    ← PowerSeries.coe_substAlgHom hX0, map_mul, map_pow, PowerSeries.coe_substAlgHom]
  exact key _ _ _ _ hm
end PI.FglChordFactor.Wk
