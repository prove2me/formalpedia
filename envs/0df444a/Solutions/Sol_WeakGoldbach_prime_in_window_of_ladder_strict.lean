-- Prove2me | solution 1 for WeakGoldbach.prime_in_window_of_ladder_strict
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T17:42:47.506753+00:00
-- url     : https://prove2.me/submissions/6f1a4299-0a59-4eee-83ee-e3c93bf39c45

import Mathlib

/-- A prime ladder whose top rung is *strictly* past `T - B` covers every window `(x, x+B)` below `T-B`. -/
theorem solution (k : ℕ) (p : ℕ → ℕ)
    (hprime : ∀ i, i ≤ k → Nat.Prime (p i))
    (h0 : p 0 ≤ 4 * 10 ^ 18)
    (hstep : ∀ i, i < k → p i < p (i + 1) ∧ p (i + 1) < p i + 4 * 10 ^ 18)
    (htop : 8875694145621773516800000000000 < p k + 4 * 10 ^ 18)
    (x : ℕ) (hx : x ≤ 8875694145621773516800000000000 - 4 * 10 ^ 18) :
    ∃ q : ℕ, x < q ∧ q < x + 4 * 10 ^ 18 ∧ Nat.Prime q := by
  classical
  rcases Nat.lt_or_ge x 2 with hx2 | hx2
  · exact ⟨2, by omega, by omega, Nat.prime_two⟩
  rcases Nat.lt_or_ge x (p 0) with hlt | hge
  · exact ⟨p 0, hlt, by omega, hprime 0 (Nat.zero_le k)⟩
  · -- the first rung is at or below x
    let S : Finset ℕ := (Finset.range (k + 1)).filter (fun i => p i ≤ x)
    have hmem0 : 0 ∈ S :=
      Finset.mem_filter.mpr ⟨by simp [Finset.mem_range], hge⟩
    have hSne : S.Nonempty := ⟨0, hmem0⟩
    set j : ℕ := S.max' hSne with hjdef
    have hjS : j ∈ S := Finset.max'_mem S hSne
    have hjk : j ≤ k := by
      have hj := (Finset.mem_filter.mp hjS).1
      simpa using hj
    have hpj : p j ≤ x := (Finset.mem_filter.mp hjS).2
    have hmax : ∀ i, i ≤ k → p i ≤ x → i ≤ j := by
      intro i hik hpi
      have hiS : i ∈ S := Finset.mem_filter.mpr ⟨by simp [Finset.mem_range]; omega, hpi⟩
      exact Finset.le_max' S i hiS
    -- the last rung is not below x, because its successor-plus-gap reaches past T
    have hlt_k : j < k := by
      by_contra hcon
      have hk : k ≤ j := by omega
      have hjkeq : j = k := le_antisymm hjk hk
      rw [← hjkeq] at htop
      omega
    obtain ⟨hs1, hs2⟩ := hstep j hlt_k
    have hxj : x < p (j + 1) := by
      by_contra hle
      have := hmax (j + 1) (by omega) (by omega)
      omega
    exact ⟨p (j + 1), hxj, by omega, hprime (j + 1) (by omega)⟩
