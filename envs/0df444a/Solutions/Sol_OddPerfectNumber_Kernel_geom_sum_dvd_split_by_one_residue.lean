-- Prove2me | solution 1 for OddPerfectNumber.Kernel.geom_sum_dvd_split_by_one_residue
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-30T17:02:34.723493+00:00
-- url     : https://prove2.me/submissions/dff2226f-564d-4766-b3f1-84e4fb296eb6

import Mathlib

theorem solution : ¬ (∀ {p q e : Nat}, p.Prime → ¬ p ∣ q →
    p ∣ (∑ i ∈ Finset.range (2 * e + 1), q ^ i) →
    ((q : ZMod p) = 1) ∨ (2 * e + 1) ∣ orderOf (q : ZMod p)) := by
  intro h
  have hbad := h (p := 7) (q := 2) (e := 4) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])
  have ho : orderOf (2 : ZMod 7) = 3 := by
    haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    exact orderOf_eq_prime (by decide) (by decide)
  rcases hbad with hbad | hbad
  · exact (by decide : (2 : ZMod 7) ≠ 1) hbad
  · norm_num [ho] at hbad
