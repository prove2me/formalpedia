-- Prove2me | solution 1 for actuarial_c_finite_assurance_annuity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-15T13:15:22.239713+00:00
-- url     : https://prove2.me/submissions/d7f92200-c33a-43a5-90a3-cc8a880e7163

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_actuarial_c_alive
import Definitions.Def_actuarial_c_death
import Definitions.Def_actuarial_c_total
import Definitions.Def_actuarial_c_surv
import Definitions.Def_actuarial_c_termPath
import Definitions.Def_actuarial_c_term
import Definitions.Def_actuarial_c_pureMass
import Definitions.Def_actuarial_c_due
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open ActuarialAssurances
private theorem death_plus_next_survivor_local (k j : ℕ) :
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
private theorem decrement_local (h j : ℕ) (p : ℕ → ℝ) (hj : j < h) : surv h p j=p j+surv h p (j+1) := by
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
          rw [death_plus_next_survivor_local]
          ring
    _ = (∑ k ∈ Finset.range (h+1), p k * death k j) +
          (∑ k ∈ Finset.range (h+1), p k * alive k (j+1)) := by
            rw [Finset.sum_add_distrib]
    _ = p j + (∑ k ∈ Finset.range (h+1),
        p k * alive k (j+1)) := by rw [hmass]
private theorem survival_zero_local (h : ℕ) (p : ℕ → ℝ) : surv h p 0=total h p := by
  unfold surv total
  apply Finset.sum_congr rfl
  intro k hk
  simp [alive]
private theorem term_mass_local (h n : ℕ) (v : ℝ) (b p : ℕ → ℝ) (hn : n ≤ h) : term h n v b p=∑ j ∈ Finset.range n, v^(j+1)*b j*p j := by
  unfold term termPath
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  have hcover : j < h :=
    lt_of_lt_of_le (Finset.mem_range.mp hj) hn
  simp only [if_pos hcover]
  have hj' : j ∈ Finset.range (h + 1) := by
    exact Finset.mem_range.mpr (Nat.lt_succ_of_lt hcover)
  calc
    (∑ k ∈ Finset.range (h+1),
      p k * (v^(j+1) * b j * death k j)) =
      ∑ k ∈ Finset.range (h+1),
        if k = j then p k * (v^(j+1) * b j) else 0 := by
        apply Finset.sum_congr rfl
        intro k hk
        by_cases hkj : k = j <;> simp [death, hkj]
    _ = p j * (v^(j+1) * b j) := by simp [hj']
    _ = v^(j+1)*b j*p j := by ring
private theorem discounted_tail_telescope_local (s : ℕ → ℝ) (v : ℝ) (n : ℕ) :
    (∑ j ∈ Finset.range n,
       (v^j * s j - v^(j+1) * s (j+1))) = s 0 - v^n * s n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      rw [pow_succ]
      ring
/-- The algebra behind the finite insurance–annuity conservation relation. -/
private theorem discounted_survival_annuity_conservation_local (s : ℕ → ℝ)
    (v : ℝ) (n : ℕ) :
    (∑ j ∈ Finset.range n,
       v^(j+1) * (s j - s (j+1))) +
      (1-v)*(∑ j ∈ Finset.range n, v^j * s j) +
      v^n * s n = s 0 := by
  have hsum :
      (∑ j ∈ Finset.range n,
         v^(j+1) * (s j - s (j+1))) +
      (1-v)*(∑ j ∈ Finset.range n, v^j * s j) =
      (∑ j ∈ Finset.range n,
         (v^j * s j - v^(j+1) * s (j+1))) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    rw [pow_succ]
    ring
  rw [hsum, discounted_tail_telescope_local]
  ring
theorem solution (h n : ℕ) (v : ℝ) (p : ℕ → ℝ) (hn : n ≤ h) (hm : total h p=1) : term h n v (fun _ => 1) p+pureMass h n v p+(1-v)*due h n v p=1 := by
  have hdec (j : ℕ) (hj : j ∈ Finset.range n) :
      p j = surv h p j - surv h p (j+1) := by
    have hjh : j < h :=
      lt_of_lt_of_le (Finset.mem_range.mp hj) hn
    have hd := decrement_local h j p hjh
    linarith
  have hmass :
      term h n v (fun _ => 1) p =
      (∑ j ∈ Finset.range n,
        v^(j+1) * (surv h p j - surv h p (j+1))) := by
    rw [term_mass_local h n v (fun _ => 1) p hn]
    apply Finset.sum_congr rfl
    intro j hj
    rw [hdec j hj]
    ring
  rw [hmass]
  unfold pureMass due
  have ht := discounted_survival_annuity_conservation_local
    (surv h p) v n
  calc
    (∑ j ∈ Finset.range n,
        v^(j+1) * (surv h p j - surv h p (j+1))) +
      v^n * surv h p n +
      (1-v) * (∑ j ∈ Finset.range n, v^j * surv h p j) =
      (∑ j ∈ Finset.range n,
        v^(j+1) * (surv h p j - surv h p (j+1))) +
      (1-v) * (∑ j ∈ Finset.range n, v^j * surv h p j) +
      v^n * surv h p n := by ring
    _ = surv h p 0 := ht
    _ = 1 := by rw [survival_zero_local, hm]
