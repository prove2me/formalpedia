-- Prove2me | solution 1 for WeightedMajority.Shattered.lemma_7_1
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T02:11:35.288983+00:00
-- url     : https://prove2.me/submissions/40a5114f-b28a-4741-86fc-632a5c83419e

import Mathlib


/-- Littlestone--Warmuth, Lemma 7.1, p. 244. The book's indices 1,...,n are
represented by `Fin n`, starting at zero. -/
theorem solution {n : ℕ} (hn : 0 < n) (r : Fin n → ℝ)
    (hr : ∀ i, 0 < r i)
    (hquot : ∀ i j : Fin n, (j : ℕ) = (i : ℕ) + 1 →
      ∃ k : ℤ, r i / r j = (k : ℝ))
    (s : ℝ) (hspos : 0 < s) (hsle : s ≤ ∑ i, r i)
    (hsint : ∃ k : ℤ, s / r ⟨0, hn⟩ = (k : ℝ)) :
    ∃ m : ℕ, m ≤ n ∧ ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < m), r i = s := by
  classical
  induction n generalizing s with
  | zero => omega
  | succ n ih =>
    have h0 : 0 < r 0 := hr 0
    obtain ⟨k, hk⟩ := hsint
    have hsk : s = (k : ℝ) * r 0 := (div_eq_iff (ne_of_gt h0)).mp hk
    have hkpos : 0 < k := by
      have : (0 : ℝ) < k := by nlinarith
      exact_mod_cast this
    have hfirst : r 0 ≤ s := by
      have : (1 : ℝ) ≤ k := by exact_mod_cast hkpos
      nlinarith
    by_cases heq : s = r 0
    · refine ⟨1, by omega, ?_⟩
      rw [Finset.sum_filter, Fin.sum_univ_succ]
      simp [heq]
    · have hres : 0 < s - r 0 := sub_pos.mpr (lt_of_le_of_ne hfirst (Ne.symm heq))
      cases n with
      | zero =>
        simp [Fin.sum_univ_succ] at hsle
        linarith
      | succ n =>
        have hn' : 0 < n + 1 := by omega
        obtain ⟨j, hj⟩ := hquot 0 (Fin.succ 0) (by simp)
        have hjr : r 0 = (j : ℝ) * r (Fin.succ 0) :=
          (div_eq_iff (ne_of_gt (hr _))).mp hj
        have hint' : ∃ l : ℤ, (s - r 0) / r (Fin.succ 0) = (l : ℝ) := by
          refine ⟨(k - 1) * j, ?_⟩
          rw [div_eq_iff (ne_of_gt (hr _))]
          push_cast
          nlinarith [hsk]
        have hle' : s - r 0 ≤ ∑ i : Fin (n + 1), r i.succ := by
          rw [Fin.sum_univ_succ] at hsle
          linarith
        obtain ⟨m, hm, hsum⟩ := ih hn' (fun i => r i.succ)
          (fun i => hr i.succ)
          (fun i j hij => hquot i.succ j.succ (by simpa using hij))
          (s-r 0) hres hle' hint'
        refine ⟨m+1, by omega, ?_⟩
        rw [Finset.sum_filter, Fin.sum_univ_succ]
        simp only [Fin.val_zero, Nat.zero_lt_succ, ↓reduceIte, Fin.val_succ,
          Nat.add_lt_add_iff_right]
        rw [← Finset.sum_filter, hsum]
        ring




#print axioms solution
