-- Prove2me | solution 1 for PI.FglTriFactor.Wk.prod_upd_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:39:51.171707+00:00
-- url     : https://prove2.me/submissions/242d8280-1c61-4ae3-8a81-a4dcc4e1c7ee

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_SubstMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupTriangles_CoeffSubstUpdZero
import Theorems.Thm_PI_FglTriFactor_Wk_upd_self
import Theorems.Thm_PI_FglTriFactor_Wk_upd_ne
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
theorem _root_.solution (k : σ) (d : σ →₀ ℕ) :
    (d.prod fun s e => (upd k (0 : MvPowerSeries σ K) s) ^ e) =
      if d k = 0 then MvPowerSeries.monomial d 1 else 0 := by
  by_cases h : d k = 0
  · rw [if_pos h, MvPowerSeries.monomial_one_eq]
    refine Finsupp.prod_congr fun s hs => ?_
    have hsk : s ≠ k := by
      rintro rfl
      exact (Finsupp.mem_support_iff.1 hs) h
    rw [upd_ne _ hsk]
  · rw [if_neg h, Finsupp.prod]
    refine Finset.prod_eq_zero (i := k) (Finsupp.mem_support_iff.2 h) ?_
    try dsimp only
    rw [upd_self, zero_pow h]
end PI.FglTriFactor.Wk
