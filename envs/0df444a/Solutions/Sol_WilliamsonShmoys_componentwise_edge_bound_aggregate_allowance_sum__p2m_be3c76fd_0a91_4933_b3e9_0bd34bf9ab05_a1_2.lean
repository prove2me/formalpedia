-- Prove2me | solution 2 for WilliamsonShmoys.componentwise_edge_bound_aggregate_allowance_sum__p2m_be3c76fd_0a91_4933_b3e9_0bd34bf9ab05_a1
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-11T11:58:43.631821+00:00
-- url     : https://prove2.me/submissions/40591271-f243-4e25-b63a-773718c0542a

import Mathlib

open scoped BigOperators

/-- If positive integers `m c` sum to `n ≥ 3`, then the total allowance
`∑ c, (if 3 ≤ m c then 3*m c - 6 else m c / 2)` is at most `3*n - 6`. -/
theorem solution {n : Nat} (C : Type) [Fintype C] (m : C → Nat) (hm : ∀ c, 0 < m c)
    (hn : 3 ≤ n) (hsum : (∑ c, m c) = n) :
    (∑ c, if 3 ≤ m c then 3 * m c - 6 else m c / 2) ≤ 3 * n - 6 := by
  have hkpos : 0 < Fintype.card C := by
    rcases Nat.eq_zero_or_pos (Fintype.card C) with hk0 | hkpos
    · exfalso
      haveI : IsEmpty C := Fintype.card_eq_zero_iff.mp hk0
      have h0 : (∑ c, m c) = 0 := by simp
      omega
    · exact hkpos
  rcases Nat.lt_or_ge (Fintype.card C) 2 with hlt | hge
  · have hcard1 : Fintype.card C = 1 := by omega
    obtain ⟨c, hc⟩ := Fintype.card_eq_one_iff.mp hcard1
    have hsumc : (∑ x, m x) = m c := by
      apply Finset.sum_eq_single c
      · intro b _ hb
        exact absurd (hc b) hb
      · intro h
        exact absurd (Finset.mem_univ c) h
    have hmc : m c = n := by rw [← hsumc]; exact hsum
    have hbig : 3 ≤ m c := by omega
    have hgoal : (∑ x, if 3 ≤ m x then 3 * m x - 6 else m x / 2) =
        (if 3 ≤ m c then 3 * m c - 6 else m c / 2) := by
      apply Finset.sum_eq_single c
      · intro b _ hb
        exact absurd (hc b) hb
      · intro h
        exact absurd (Finset.mem_univ c) h
    rw [hgoal, if_pos hbig, hmc]
  · have hterm : ∀ c, (if 3 ≤ m c then 3 * m c - 6 else m c / 2) ≤ 3 * m c - 3 := by
      intro c
      have hpos : 0 < m c := hm c
      rcases le_or_gt 3 (m c) with h3 | h3
      · rw [if_pos h3]
        omega
      · rw [if_neg (not_le.mpr h3)]
        have h1 : m c = 1 ∨ m c = 2 := by omega
        rcases h1 with h1 | h1 <;> simp [h1]
    have hsum_le : (∑ c, (if 3 ≤ m c then 3 * m c - 6 else m c / 2)) ≤
        ∑ c, (3 * m c - 3) :=
      Finset.sum_le_sum (fun c _ => hterm c)
    have hdistr : (∑ c, (3 * m c - 3)) = 3 * n - 3 * Fintype.card C := by
      rw [Finset.sum_tsub_distrib]
      · rw [← Finset.mul_sum, Finset.sum_const, Finset.card_univ, hsum]
        rw [Nat.nsmul_eq_mul]
        omega
      · intro c _
        have hpos : 0 < m c := hm c
        omega
    have hcard : 6 ≤ 3 * Fintype.card C := by omega
    have hfin : 3 * n - 3 * Fintype.card C ≤ 3 * n - 6 :=
      Nat.sub_le_sub_left hcard (3 * n)
    omega
