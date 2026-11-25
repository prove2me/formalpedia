-- Prove2me | solution 1 for PI.UG.W.hStd_eStd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:32:20.301669+00:00
-- url     : https://prove2.me/submissions/35ca9421-1bf1-45d7-932e-c921e5d43c0d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularGenus_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularGenus_StdLatEqSpan
import Theorems.Thm_PI_UG_W_hStd_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
noncomputable section
open PI PI.UG PI.UG.W
namespace PI.UG.W
theorem _root_.solution (E : Type) [Field E] [StarRing E] (n : ℕ) (i j : Fin n) :
    hStd E n (eStd E n i) (eStd E n j) = if i = j then 1 else 0 := by
  rw [hStd_apply]
  by_cases h : i = j
  · subst h
    rw [Finset.sum_eq_single i (fun k _ hk => by simp [eStd, hk]) (by simp)]
    simp [eStd]
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : k = i
    · subst hk
      simp [eStd, Ne.symm h]
    · simp [eStd, Pi.single_apply, hk]
end PI.UG.W
