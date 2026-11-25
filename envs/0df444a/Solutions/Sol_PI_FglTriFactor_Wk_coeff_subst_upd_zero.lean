-- Prove2me | solution 1 for PI.FglTriFactor.Wk.coeff_subst_upd_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:46:37.33785+00:00
-- url     : https://prove2.me/submissions/a2212705-86a5-4a0e-b079-16785e9fd849

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_SubstMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupTriangles_CoeffSubstUpdZero
import Theorems.Thm_PI_FglTriFactor_Wk_hasSubst_upd
import Theorems.Thm_PI_FglTriFactor_Wk_prod_upd_zero
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
theorem _root_.solution (k : σ) (f : MvPowerSeries σ K) (m : σ →₀ ℕ) (hm : m k = 0) :
    MvPowerSeries.coeff m (MvPowerSeries.subst (upd k (0 : MvPowerSeries σ K)) f) = MvPowerSeries.coeff m f := by
  have ha := hasSubst_upd k (t := (0 : MvPowerSeries σ K)) (map_zero _)
  rw [MvPowerSeries.coeff_subst ha, finsum_eq_single _ m]
  · try dsimp only
    rw [prod_upd_zero, if_pos hm, MvPowerSeries.coeff_monomial_same, smul_eq_mul, mul_one]
  · intro d hd
    try dsimp only
    rw [prod_upd_zero]
    split_ifs
    · rw [MvPowerSeries.coeff_monomial_ne (Ne.symm hd), smul_zero]
    · rw [map_zero, smul_zero]
end PI.FglTriFactor.Wk
