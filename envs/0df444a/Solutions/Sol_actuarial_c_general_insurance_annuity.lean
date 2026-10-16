-- Prove2me | solution 1 for actuarial_c_general_insurance_annuity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-15T12:59:00.020228+00:00
-- url     : https://prove2.me/submissions/ac388da0-5d63-4be3-8f96-b9d1184ea4ce

import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Definitions.Def_actuarial_c_alive
import Definitions.Def_actuarial_c_death
import Definitions.Def_actuarial_c_surv
import Definitions.Def_actuarial_c_path
import Definitions.Def_actuarial_c_epv
import Definitions.Def_actuarial_c_massPV
import Definitions.Def_actuarial_c_weightedDue
import Definitions.Def_actuarial_c_differenceBenefit
import Theorems.Thm_actuarial_c_epv_equals_mass
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open ActuarialAssurances
private theorem death_plus_next_survivor (k j : ℕ) :
    alive k j = death k j + alive k (j+1) := by
  by_cases heq : k = j
  · subst k
    simp [alive, death]
  · by_cases hlt : k < j
    · have hjnot : ¬ j ≤ k := not_le.mpr hlt
      have hj1not : ¬ j + 1 ≤ k :=
        not_le.mpr (Nat.lt_trans hlt (Nat.lt_succ_self j))
      simp [alive, death, heq, hjnot, hj1not]
    · have hjle : j ≤ k := Nat.le_of_not_gt hlt
      have hjlt : j < k := lt_of_le_of_ne hjle (Ne.symm heq)
      have hj1le : j + 1 ≤ k := Nat.succ_le_iff.mpr hjlt
      simp [alive, death, heq, hjle, hj1le]

private theorem decrement (h j : ℕ) (p : ℕ → ℝ) (hj : j < h) : surv h p j=p j+surv h p (j+1) := by
  have hmem : j ∈ Finset.range (h+1) := by
    exact Finset.mem_range.mpr (Nat.lt_succ_of_lt hj)
  have hmass : (∑ k ∈ Finset.range (h+1), p k * death k j) = p j := by
    calc
      (∑ k ∈ Finset.range (h+1), p k * death k j) =
        ∑ k ∈ Finset.range (h+1), if k = j then p k else 0 := by
          apply Finset.sum_congr rfl
          intro k hk
          by_cases hkj : k = j <;> simp [death, hkj]
      _ = p j := by simp [hmem]
  unfold surv
  calc
    (∑ k ∈ Finset.range (h+1), p k * alive k j) =
      ∑ k ∈ Finset.range (h+1),
        (p k * death k j + p k * alive k (j+1)) := by
          apply Finset.sum_congr rfl
          intro k hk
          rw [death_plus_next_survivor]
          ring
    _ = (∑ k ∈ Finset.range (h+1), p k * death k j) +
          (∑ k ∈ Finset.range (h+1), p k * alive k (j+1)) := by
            rw [Finset.sum_add_distrib]
    _ = p j + (∑ k ∈ Finset.range (h+1),
        p k * alive k (j+1)) := by rw [hmass]

private theorem weighted_survival_summation_by_parts
    (b f : ℕ → ℝ) (n : ℕ) :
    (∑ j ∈ Finset.range (n+1), b j * (f j - f (j+1))) +
      b n * f (n+1) =
      b 0 * f 0 +
        ∑ j ∈ Finset.range n, (b (j+1) - b j) * f (j+1) := by
  induction n with
  | zero =>
      simp only [Finset.sum_range_zero, Finset.sum_range_succ,
        zero_add, mul_zero, add_zero]
      ring
  | succ n ih =>
      calc
        (∑ j ∈ Finset.range (n+1+1),
            b j * (f j - f (j+1))) + b (n+1) * f (n+1+1) =
          ((∑ j ∈ Finset.range (n+1),
              b j * (f j - f (j+1))) + b n * f (n+1)) +
            (b (n+1)-b n)*f (n+1) := by
              rw [Finset.sum_range_succ]
              ring
        _ = b 0 * f 0 +
              (∑ j ∈ Finset.range n,
                (b (j+1)-b j)*f (j+1)) +
              (b (n+1)-b n)*f (n+1) := by rw [ih]
        _ = b 0 * f 0 +
              ∑ j ∈ Finset.range (n+1),
                (b (j+1)-b j)*f (j+1) := by
              rw [Finset.sum_range_succ]
              ring

theorem solution (h : ℕ) (v : ℝ) (b p : ℕ → ℝ) : epv h v b p+(1-v)*weightedDue h v b p+v^h*b (h-1)*surv h p h=differenceBenefit h v b p := by
  rw [actuarial_c_epv_equals_mass]
  unfold massPV weightedDue differenceBenefit
  cases h with
  | zero =>
      simp
  | succ m =>
      have hdec (j : ℕ) (hj : j ∈ Finset.range (m+1)) :
          p j = surv (m+1) p j - surv (m+1) p (j+1) := by
        have hd := decrement (m+1) j p (Finset.mem_range.mp hj)
        linarith [hd]
      have hsum :
          (∑ j ∈ Finset.range (m+1), v^(j+1)*b j*p j) +
            (1-v)*(∑ j ∈ Finset.range (m+1),
              b j*v^j*surv (m+1) p j) =
          (∑ j ∈ Finset.range (m+1),
            b j * (v^j*surv (m+1) p j -
              v^(j+1)*surv (m+1) p (j+1))) := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j hj
        rw [hdec j hj, pow_succ]
        ring
      rw [hsum]
      have htel := weighted_survival_summation_by_parts
        b (fun j => v^j * surv (m+1) p j) m
      simpa only [Nat.succ_eq_add_one, Nat.add_sub_cancel_right,
        pow_zero, one_mul, mul_one, mul_assoc, mul_left_comm, mul_comm] using htel
