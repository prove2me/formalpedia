-- Prove2me | solution 1 for actuarial_c_endow_mass
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-14T07:28:17.887612+00:00
-- url     : https://prove2.me/submissions/306f563d-d74d-42ad-862f-32070f079063

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Definitions.Def_actuarial_c_alive
import Definitions.Def_actuarial_c_death
import Definitions.Def_actuarial_c_surv
import Definitions.Def_actuarial_c_termPath
import Definitions.Def_actuarial_c_purePath
import Definitions.Def_actuarial_c_endowPath
import Definitions.Def_actuarial_c_endow

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialAssurances

theorem solution (h n : ℕ) (v : ℝ) (b p : ℕ → ℝ) (hn : n ≤ h) :
    endow h n v b p =
      (∑ j ∈ Finset.range n, v^(j+1)*b j*p j) + v^n*surv h p n := by
  have ht :
      (∑ k ∈ Finset.range (h+1), p k*termPath h n v b k) =
      ∑ j ∈ Finset.range n, v^(j+1)*b j*p j := by
    unfold termPath
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    have hcover : j < h :=
      lt_of_lt_of_le (Finset.mem_range.mp hj) hn
    simp only [if_pos hcover]
    have hjmem : j ∈ Finset.range (h + 1) :=
      Finset.mem_range.mpr (Nat.lt_succ_of_lt hcover)
    calc
      (∑ k ∈ Finset.range (h+1),
        p k * (v^(j+1) * b j * death k j)) =
        ∑ k ∈ Finset.range (h+1),
          if k = j then p k * (v^(j+1) * b j) else 0 := by
          apply Finset.sum_congr rfl
          intro k hk
          by_cases hkj : k = j <;> simp [death, hkj]
      _ = p j * (v^(j+1) * b j) := by simp [hjmem]
      _ = v^(j+1)*b j*p j := by ring
  have hp :
      (∑ k ∈ Finset.range (h+1), p k*purePath n k v) =
      v^n*surv h p n := by
    unfold purePath surv
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  unfold endow endowPath
  calc
    (∑ k ∈ Finset.range (h+1),
      p k * (termPath h n v b k + purePath n k v)) =
      (∑ k ∈ Finset.range (h+1), p k*termPath h n v b k) +
      (∑ k ∈ Finset.range (h+1), p k*purePath n k v) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro k hk
        ring
    _ = (∑ j ∈ Finset.range n, v^(j+1)*b j*p j) +
      v^n*surv h p n := by rw [ht, hp]
