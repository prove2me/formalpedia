-- Prove2me | solution 1 for actuarial_c_net_premium_zero_expected_loss
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-14T07:40:54.746666+00:00
-- url     : https://prove2.me/submissions/6173a09d-84c1-4340-a419-1767885da4fc

import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Definitions.Def_actuarial_c_alive
import Definitions.Def_actuarial_c_death
import Definitions.Def_actuarial_c_surv
import Definitions.Def_actuarial_c_termPath
import Definitions.Def_actuarial_c_term
import Definitions.Def_actuarial_c_due
import Definitions.Def_actuarial_c_premiumPath
import Definitions.Def_actuarial_c_lossPath
import Definitions.Def_actuarial_c_expectedLoss
import Definitions.Def_actuarial_c_netPremium

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialAssurances

theorem solution (h n : ℕ) (v : ℝ) (b p : ℕ → ℝ)
    (ha : 0 < due h n v p) :
    expectedLoss h n v (netPremium h n v b p) b p = 0 := by
  have hpremium :
      (∑ k ∈ Finset.range (h+1), p k*premiumPath n v k) =
        due h n v p := by
    unfold premiumPath due surv
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro k hk
    ring
  have hloss (premium : ℝ) :
      expectedLoss h n v premium b p =
        term h n v b p - premium * due h n v p := by
    unfold expectedLoss lossPath term
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib]
    have hz : (∑ k ∈ Finset.range (h+1),
        p k * (premium * premiumPath n v k)) =
        premium * (∑ k ∈ Finset.range (h+1),
          p k * premiumPath n v k) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    rw [hz, hpremium]
  have hbalance :
      netPremium h n v b p * due h n v p = term h n v b p := by
    unfold netPremium
    have hne : due h n v p ≠ 0 := ne_of_gt ha
    field_simp [hne]
  rw [hloss, hbalance]
  ring
