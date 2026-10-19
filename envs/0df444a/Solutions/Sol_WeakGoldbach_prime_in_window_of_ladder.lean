-- Prove2me | solution 1 for WeakGoldbach.prime_in_window_of_ladder
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-18T15:50:50.590986+00:00
-- url     : https://prove2.me/submissions/afdfa208-2af6-47a6-b37c-1c1a2316d99f

import Mathlib

theorem solution (k : ℕ) (p : ℕ → ℕ) (n : ℕ)
    (hprime : ∀ i, i ≤ k → Nat.Prime (p i) ∧ Odd (p i))
    (h0 : p 0 ≤ 4 * 10 ^ 18)
    (hstep : ∀ i, i < k → p i < p (i + 1) ∧ p (i + 1) < p i + 4 * 10 ^ 18)
    (htop : 8875694145621773516800000000000 ≤ p k + 4 * 10 ^ 18)
    (_hodd : Odd n)
    (hlo : 4 * 10 ^ 18 + 5 ≤ n)
    (hhi : n ≤ 8875694145621773516800000000000) :
    ∃ q : ℕ, Nat.Prime q ∧ 4 ≤ n - q ∧ n - q ≤ 4 * 10 ^ 18 + 2 := by
  classical
  -- ladder indices whose prime still lies at or below n - 4
  let S : Finset ℕ := (Finset.range (k + 1)).filter (fun i => p i ≤ n - 4)
  have hmem0 : 0 ∈ S := by
    simp only [S, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, by omega⟩
  have hSne : S.Nonempty := ⟨0, hmem0⟩
  set j : ℕ := S.max' hSne with hjdef
  have hjS : j ∈ S := Finset.max'_mem S hSne
  have hjk : j ≤ k := by
    have hj := (Finset.mem_filter.mp hjS).1
    simpa using hj
  have hpj : p j ≤ n - 4 := (Finset.mem_filter.mp hjS).2
  -- j is the largest such index
  have hmax : ∀ i, i ≤ k → p i ≤ n - 4 → i ≤ j := by
    intro i hik hpi
    have hiS : i ∈ S := by
      simp only [S, Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, hpi⟩
    exact Finset.le_max' S i hiS
  have hpjn : p j ≤ n := by omega
  set r : ℕ := n - p j with hrdef
  have hsum : p j + r = n := by omega
  -- the gap from the chosen rung is at most B + 2
  have hrle : r ≤ 4 * 10 ^ 18 + 2 := by
    by_contra hcon
    have hrge : 4 * 10 ^ 18 + 3 ≤ r := by omega
    rcases Nat.lt_or_ge j k with hjk' | hjk'
    · obtain ⟨hs1, hs2⟩ := hstep j hjk'
      have hnot : ¬ (p (j + 1) ≤ n - 4) := by
        intro hle
        have hle' : j + 1 ≤ j := hmax (j + 1) (by omega) hle
        omega
      have hx1 : n - 3 ≤ p (j + 1) := by omega
      have hpad : p j + 4 * 10 ^ 18 ≤ n - 3 := by omega
      have hx2 : p (j + 1) < n - 3 := by omega
      omega
    · have hjk_eq : k = j := by omega
      rw [hjk_eq] at htop
      have hbk : p j + 4 * 10 ^ 18 < n - 2 := by omega
      omega
  exact ⟨p j, (hprime j hjk).1, by omega, by omega⟩
