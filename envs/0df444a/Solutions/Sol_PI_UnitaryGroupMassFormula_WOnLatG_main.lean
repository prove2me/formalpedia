-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.WOnLatG.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:18:12.46134+00:00
-- url     : https://prove2.me/submissions/13bf7f9f-32cd-4ba6-97df-23744803ee1c

import Definitions.Def_Formalism_PeriodIntegrals_WOnLatG
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilLatticeAction_NegOneZpowOddMul
import Theorems.Thm_PI_UnitaryGroupMassFormula_WOnLatG_exp_pi_int
import Theorems.Thm_PI_UnitaryGroupMassFormula_WOnLatG_neg_one_zpow_odd_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.WOnLatG
open PI.WPhDefs
namespace PI.UnitaryGroupMassFormula.WOnLatG
theorem _root_.solution : PI.WOnLatG := by
  intro T I J _ _ _ s A La' hLa p hp x hx
  obtain ⟨m, hm⟩ := (hLa x hx).1
  have hal : alG s A x = (-1 : ℂ) ^ m := by
    have : s * (HfG A x x).re = (m : ℝ) := hm
    simp only [alG, this, round_intCast]
  rw [hal]
  unfold wPhG
  split_ifs with h2
  · rw [hm]; exact exp_pi_int m
  · have hne : ∃ c : ℂ, ∃ (k : ℕ) (m' : ℤ), (p : ℝ) ^ k * qG s A x = (m' : ℝ) ∧ c = (-1 : ℂ) ^ m' :=
      ⟨(-1 : ℂ) ^ m, 0, m, by rw [hm]; simp, rfl⟩
    obtain ⟨k, m', hk, hc⟩ := Classical.epsilon_spec hne
    rw [hc]
    rw [hm] at hk
    have hm' : m' = (p : ℤ) ^ k * m := by
      have : ((m' : ℤ) : ℝ) = (((p : ℤ) ^ k * m : ℤ) : ℝ) := by rw [← hk]; push_cast; ring
      exact_mod_cast this
    have hodd : Odd ((p : ℤ) ^ k) := by
      have : Odd p := hp.odd_of_ne_two h2
      exact (Int.odd_coe_nat p |>.2 this).pow
    rw [hm', neg_one_zpow_odd_mul hodd]
end PI.UnitaryGroupMassFormula.WOnLatG
