-- Prove2me | solution 1 for PI.FglTriFactor.Wk.fact_div
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:53:24.212494+00:00
-- url     : https://prove2.me/submissions/1ced479b-bfcb-4cb1-ad30-f5bf077d0f52

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_SubstMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupTriangles_CoeffSubstUpdZero
import Theorems.Thm_PI_FglTriFactor_Wk_upd_const
import Theorems.Thm_PI_FglTriFactor_Wk_hasSubst_upd
import Theorems.Thm_PI_FglTriFactor_Wk_upd_self
import Theorems.Thm_PI_FglTriFactor_Wk_upd_ne
import Theorems.Thm_P2M_PI_FglTriFactor_Wk_X_mem_SerS__cfa52566366e
import Theorems.Thm_PI_FglTriFactor_Wk_upd_mem
import Theorems.Thm_PI_FglTriFactor_Wk_coeff_subst_upd_zero
import Theorems.Thm_PI_FglTriFactor_Wk_coeff_X_mul_shift
import Theorems.Thm_PI_AddIntG_Wk_mem_SerS
import Theorems.Thm_PI_AddIntG_Wk_mvsubst_mem_SerS

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace PI.FglTriFactor.Wk
open PI.AddIntG.Wk (SerS mem_SerS mvsubst_mem_SerS)
variable {K : Type*} [Field K] {σ : Type*} [Finite σ] [DecidableEq σ]
private theorem subst_upd_subst_upd_eq_subst_upd_subst (k : σ) {t u : MvPowerSeries σ K}
    (ht : MvPowerSeries.constantCoeff t = 0) (hu : MvPowerSeries.constantCoeff u = 0) (F : MvPowerSeries σ K) :
    MvPowerSeries.subst (upd k u) (MvPowerSeries.subst (upd k t) F) =
      MvPowerSeries.subst (upd k (MvPowerSeries.subst (upd k u) t)) F := by
  rw [MvPowerSeries.subst_comp_subst_apply (hasSubst_upd k ht) (hasSubst_upd k hu)]
  congr 1
  funext i
  try dsimp only
  rcases eq_or_ne i k with rfl | h
  · rw [upd_self, upd_self]
  · rw [upd_ne t h, upd_ne _ h, MvPowerSeries.subst_X (hasSubst_upd k hu),
      upd_ne u h]
end PI.FglTriFactor.Wk
end
end

set_option autoImplicit false
noncomputable section
open PI PI.FglTriFactor PI.FglTriFactor.Wk
open PI.AddIntG.Wk (SerS mem_SerS mvsubst_mem_SerS)
variable {K : Type*} [Field K] {σ : Type*} [Finite σ] [DecidableEq σ]
namespace PI.FglTriFactor.Wk
theorem _root_.solution {S : Subring K} {k : σ} {s G : MvPowerSeries σ K}
    (hs0 : MvPowerSeries.constantCoeff s = 0) (hsS : s ∈ SerS S σ)
    (hsk : ∀ t : MvPowerSeries σ K, MvPowerSeries.constantCoeff t = 0 → MvPowerSeries.subst (upd k t) s = s)
    (hG : G ∈ SerS S σ) (hz : MvPowerSeries.subst (upd k s) G = 0) :
    ∃ H ∈ SerS S σ, G = (MvPowerSeries.X k - s) * H := by
  have hz0 : MvPowerSeries.constantCoeff (0 : MvPowerSeries σ K) = 0 := map_zero _
  have hp0 : MvPowerSeries.constantCoeff (MvPowerSeries.X k + s : MvPowerSeries σ K) = 0 := by
    rw [map_add, hs0, add_zero]; exact MvPowerSeries.constantCoeff_X k
  have hm0 : MvPowerSeries.constantCoeff (MvPowerSeries.X k - s : MvPowerSeries σ K) = 0 := by
    rw [map_sub, hs0, sub_zero]; exact MvPowerSeries.constantCoeff_X k
  have hG' : MvPowerSeries.subst (upd k (MvPowerSeries.X k + s)) G ∈ PI.AddIntG.Wk.SerS S σ :=
    PI.AddIntG.Wk.mvsubst_mem_SerS S (upd_const hp0)
      (upd_mem k (add_mem (X_mem_SerS' S k) hsS)) hG
  have e0 : MvPowerSeries.subst (upd k (0 : MvPowerSeries σ K)) (MvPowerSeries.X k + s) = s := by
    rw [MvPowerSeries.subst_add (hasSubst_upd k hz0), MvPowerSeries.subst_X (hasSubst_upd k hz0),
      upd_self, hsk 0 hz0, zero_add]
  have hdvd : (MvPowerSeries.X k : MvPowerSeries σ K) ∣ MvPowerSeries.subst (upd k (MvPowerSeries.X k + s)) G := by
    rw [MvPowerSeries.X_dvd_iff]
    intro m hm
    rw [← coeff_subst_upd_zero k _ m hm, subst_upd_subst_upd_eq_subst_upd_subst k hp0 hz0, e0, hz, map_zero]
  obtain ⟨H', hH'⟩ := hdvd
  have hH'S : H' ∈ PI.AddIntG.Wk.SerS S σ := by
    rw [PI.AddIntG.Wk.mem_SerS]
    intro e
    rw [← coeff_X_mul_shift k H' e, ← hH']
    exact (PI.AddIntG.Wk.mem_SerS S _).1 hG' _
  refine ⟨MvPowerSeries.subst (upd k (MvPowerSeries.X k - s)) H',
    PI.AddIntG.Wk.mvsubst_mem_SerS S (upd_const hm0)
      (upd_mem k (sub_mem (X_mem_SerS' S k) hsS)) hH'S, ?_⟩
  have e1 : MvPowerSeries.subst (upd k (MvPowerSeries.X k - s)) (MvPowerSeries.X k + s) = MvPowerSeries.X k := by
    rw [MvPowerSeries.subst_add (hasSubst_upd k hm0), MvPowerSeries.subst_X (hasSubst_upd k hm0),
      upd_self, hsk _ hm0, sub_add_cancel]
  have e2 : upd k (MvPowerSeries.X k : MvPowerSeries σ K) = MvPowerSeries.X := by
    funext i
    rcases eq_or_ne i k with rfl | h
    · exact upd_self _ _
    · exact upd_ne _ h
  calc G = MvPowerSeries.subst (MvPowerSeries.X : σ → MvPowerSeries σ K) G :=
        (congrFun (MvPowerSeries.subst_self (σ := σ) (R := K)) G).symm
    _ = MvPowerSeries.subst (upd k (MvPowerSeries.X k - s))
          (MvPowerSeries.subst (upd k (MvPowerSeries.X k + s)) G) := by
        rw [subst_upd_subst_upd_eq_subst_upd_subst k hp0 hm0, e1, e2]
    _ = (MvPowerSeries.X k - s) * MvPowerSeries.subst (upd k (MvPowerSeries.X k - s)) H' := by
        rw [hH', MvPowerSeries.subst_mul (hasSubst_upd k hm0), MvPowerSeries.subst_X (hasSubst_upd k hm0),
          upd_self]
end PI.FglTriFactor.Wk
