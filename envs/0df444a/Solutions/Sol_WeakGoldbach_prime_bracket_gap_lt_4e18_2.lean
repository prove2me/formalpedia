-- Prove2me | solution 2 for WeakGoldbach.prime_bracket_gap_lt_4e18
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T17:56:24.94177+00:00
-- url     : https://prove2.me/submissions/07a1175a-5b02-40c5-8ad6-b823a0015a9d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_WeakGoldbach_prime_ladder_to_8875e30_strict

theorem solution (x : Nat)
    (_hxl : Nat.le (10 ^ 26) x)
    (hx : Nat.le x (8875694145621773516800000000000 - 4 * 10 ^ 18)) :
    Exists fun p : Nat => Exists fun q : Nat =>
      And (Nat.Prime p) (And (Nat.Prime q) (And (Nat.le p x)
        (And (Nat.lt x q) (Nat.lt (Nat.sub q p) (4 * 10 ^ 18))))) := by
  obtain ⟨k, p, hprime, h0, hstep, htop⟩ := WeakGoldbach.prime_ladder_to_8875e30_strict
  simp only [Nat.le_eq] at _hxl hx
  classical
  let S : Finset ℕ := (Finset.range (k + 1)).filter (fun i => p i ≤ x)
  have hmem0 : 0 ∈ S := Finset.mem_filter.mpr ⟨by simp [Finset.mem_range], by omega⟩
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
  have hgap : p (j + 1) - p j < 4 * 10 ^ 18 := by omega
  exact ⟨p j, p (j + 1), hprime j hjk, hprime (j + 1) (by omega), hpj, hxj, hgap⟩
