-- Prove2me | solution 1 for actuarial_c_mass_to_public_commutation_M
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-14T07:25:33.710619+00:00
-- url     : https://prove2.me/submissions/eb63e436-7de6-4c37-8acf-f9062d9372ad

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_actuarial_c_alive
import Definitions.Def_actuarial_c_death
import Definitions.Def_actuarial_c_surv
import Definitions.Def_actuarial_c_massPV
import Definitions.Def_actuarial_c_massCohort
import Definitions.Def_actuarial_faM

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialAssurances

theorem solution (h : ℕ) (v : ℝ) (p : ℕ → ℝ) :
    massPV h v (fun _ => 1) p =
      ActuarialFoundations.faM (massCohort h p) v h 0 := by
  have hpart (k j : ℕ) : alive k j = death k j + alive k (j+1) := by
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
  have hdec (j : ℕ) (hj : j < h) :
      surv h p j = p j + surv h p (j+1) := by
    have hmem : j ∈ Finset.range (h+1) :=
      Finset.mem_range.mpr (Nat.lt_succ_of_lt hj)
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
            rw [hpart]
            ring
      _ = (∑ k ∈ Finset.range (h+1), p k * death k j) +
          (∑ k ∈ Finset.range (h+1), p k * alive k (j+1)) := by
            rw [Finset.sum_add_distrib]
      _ = p j + (∑ k ∈ Finset.range (h+1),
          p k * alive k (j+1)) := by rw [hmass]
  unfold massPV ActuarialFoundations.faM
  simp only [Nat.sub_zero, zero_add]
  apply Finset.sum_congr rfl
  intro j hj
  have hrec := hdec j (Finset.mem_range.mp hj)
  unfold ActuarialFoundations.faDiscountedDeaths ActuarialFoundations.faDeaths
  unfold massCohort
  have he : surv h p j - surv h p (j+1) = p j := by
    linarith
  rw [he]
  ring
