-- Prove2me | solution 1 for actuarial_c_delay_nonincrease
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-14T07:44:14.878708+00:00
-- url     : https://prove2.me/submissions/8d60c51a-16d0-4bc4-a5d0-3667391c31f9

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring
import Definitions.Def_actuarial_c_death
import Definitions.Def_actuarial_c_delayPath
import Definitions.Def_actuarial_c_delayEPV

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialAssurances

theorem solution (h a b : ℕ) (v : ℝ) (benefit p : ℕ → ℝ)
    (hab : a ≤ b) (hv : 0 ≤ v) (hv1 : v ≤ 1)
    (hb : ∀ j, 0 ≤ benefit j) (hp : ∀ j, 0 ≤ p j) :
    delayEPV h b v benefit p ≤ delayEPV h a v benefit p := by
  have hpow_one (k : ℕ) : v^k ≤ 1 := by
    induction k with
    | zero => simp
    | succ k ih =>
      calc
        v^(k+1) = v^k * v := pow_succ v k
        _ ≤ v^k * 1 :=
          mul_le_mul_of_nonneg_left hv1 (pow_nonneg hv k)
        _ = v^k := mul_one _
        _ ≤ 1 := ih
  have hdiscount (j : ℕ) : v^(j+1+b) ≤ v^(j+1+a) := by
    have hindex : j+1+b = (j+1+a)+(b-a) := by
      simp only [Nat.add_assoc, Nat.add_sub_of_le hab]
    calc
      v^(j+1+b) = v^(j+1+a)*v^(b-a) := by
        rw [hindex, pow_add]
      _ ≤ v^(j+1+a)*1 :=
        mul_le_mul_of_nonneg_left (hpow_one (b-a))
          (pow_nonneg hv _)
      _ = v^(j+1+a) := mul_one _
  have hpath (k : ℕ) :
      delayPath h b v benefit k ≤ delayPath h a v benefit k := by
    unfold delayPath
    apply Finset.sum_le_sum
    intro j hj
    have hd : 0 ≤ death k j := by
      by_cases he : k = j <;> simp [death, he]
    have hfactor : 0 ≤ benefit j * death k j :=
      mul_nonneg (hb j) hd
    calc
      v^(j+1+b)*benefit j*death k j =
        v^(j+1+b)*(benefit j*death k j) := by ring
      _ ≤ v^(j+1+a)*(benefit j*death k j) :=
        mul_le_mul_of_nonneg_right (hdiscount j) hfactor
      _ = v^(j+1+a)*benefit j*death k j := by ring
  unfold delayEPV
  apply Finset.sum_le_sum
  intro k hk
  exact mul_le_mul_of_nonneg_left (hpath k) (hp k)
