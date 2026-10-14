-- Prove2me | solution 1 for actuarial_c_endowment_second_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-14T07:45:25.159438+00:00
-- url     : https://prove2.me/submissions/fbe21f40-2e16-4061-95f9-9656f163a1a7

import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Definitions.Def_actuarial_c_alive
import Definitions.Def_actuarial_c_death
import Definitions.Def_actuarial_c_surv
import Definitions.Def_actuarial_c_termPath
import Definitions.Def_actuarial_c_purePath
import Definitions.Def_actuarial_c_endowPath
import Definitions.Def_actuarial_c_termSecond
import Definitions.Def_actuarial_c_endowSecond

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialAssurances

theorem solution (h n : ℕ) (v : ℝ) (b p : ℕ → ℝ) (hn : n ≤ h) : endowSecond h n v b p=termSecond h n v b p+v^(2*n)*surv h p n := by
  have hdisjoint (k : ℕ) :
      termPath h n v b k * purePath n k v = 0 := by
    by_cases hk : k < n
    · have hno : ¬ n ≤ k := Nat.not_le.mpr hk
      simp [purePath, alive, hno]
    · have hkge : n ≤ k := Nat.le_of_not_gt hk
      have hterm : termPath h n v b k=0 := by
        unfold termPath
        apply Finset.sum_eq_zero
        intro j hj
        have hjlt : j < n := Finset.mem_range.mp hj
        have hneq : k ≠ j := by
          intro hkj
          exact (Nat.not_le.mpr hjlt) (hkj ▸ hkge)
        by_cases jh : j < h <;> simp [jh, death, hneq]
      rw [hterm]
      ring
  have hpure (k : ℕ) :
      (purePath n k v)^2 = v^(2*n) * alive k n := by
    by_cases hk : n ≤ k
    · simp only [purePath, alive, if_pos hk, mul_one]
      rw [← pow_mul]
      rw [Nat.mul_comm n 2]
    · simp [purePath, alive, hk]
  unfold endowSecond termSecond
  change (∑ k ∈ Finset.range (h+1),
      p k * (termPath h n v b k + purePath n k v)^2) =
      (∑ k ∈ Finset.range (h+1),
        p k * (termPath h n v b k)^2) +
        v^(2*n) * surv h p n
  unfold surv
  calc
    (∑ k ∈ Finset.range (h+1),
       p k * (termPath h n v b k + purePath n k v)^2) =
      (∑ k ∈ Finset.range (h+1),
         (p k*(termPath h n v b k)^2 +
          v^(2*n)*(p k*alive k n))) := by
      apply Finset.sum_congr rfl
      intro k hk
      have hh := hdisjoint k
      calc
        p k * (termPath h n v b k + purePath n k v)^2 =
          p k * (termPath h n v b k)^2 +
            p k * (purePath n k v)^2 := by
              calc
                p k * (termPath h n v b k + purePath n k v)^2 =
                  p k * (termPath h n v b k)^2 +
                    p k * (purePath n k v)^2 +
                      2*p k*(termPath h n v b k * purePath n k v) := by ring
                _ = _ := by rw [hh]; ring
        _ = p k * (termPath h n v b k)^2 +
            v^(2*n) * (p k * alive k n) := by
              rw [hpure k]
              ring
    _ = (∑ k ∈ Finset.range (h+1),
         p k * (termPath h n v b k)^2) +
          v^(2*n)*(∑ k ∈ Finset.range (h+1),p k*alive k n) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
