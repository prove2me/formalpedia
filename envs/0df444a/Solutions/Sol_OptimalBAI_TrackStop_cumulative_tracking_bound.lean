-- Prove2me | solution 1 for OptimalBAI.TrackStop.cumulative_tracking_bound
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T06:59:39.011012+00:00
-- url     : https://prove2.me/submissions/06dd5d98-a441-4b11-b51a-80c6b6fda034

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Tactic

open scoped BigOperators
set_option autoImplicit false

theorem solution {K : ℕ} (hK : 0 < K) (n : ℕ) (hn : 0 < n)
    (p : ℕ → Fin K → ℝ)
    (hp : ∀ k, 1 ≤ k → k ≤ n → (∀ a, 0 ≤ p k a) ∧ ∑ a, p k a = 1)
    (N : ℕ → Fin K → ℝ) (I : ℕ → Fin K)
    (hN0 : N 0 = 0)
    (hI : ∀ k, k < n → ∀ i : Fin K,
      (∑ j ∈ Finset.Icc 1 (k + 1), p j i) - N k i ≤
        (∑ j ∈ Finset.Icc 1 (k + 1), p j (I (k + 1))) - N k (I (k + 1)))
    (hN : ∀ k, k < n → N (k + 1) = N k + Pi.single (I (k + 1)) (1 : ℝ)) :
    ∀ i : Fin K, |N n i - ∑ j ∈ Finset.Icc 1 n, p j i| ≤ (K : ℝ) - 1 := by
  let P : ℕ → Fin K → ℝ := fun k i => ∑ j ∈ Finset.Icc 1 k, p j i
  have hP0 : ∀ i, P 0 i = 0 := by simp [P]
  have hPstep : ∀ k i, P (k+1) i = P k i + p (k+1) i := by
    intro k i
    dsimp [P]
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ k+1)]
  have hPsum : ∀ k, k ≤ n → ∑ i, P k i = (k : ℝ) := by
    intro k
    induction k with
    | zero => simp [P]
    | succ k ih =>
      intro hk
      simp_rw [hPstep]
      rw [Finset.sum_add_distrib, ih (by omega), (hp (k+1) (by omega) hk).2]
      simp
  have hNsum : ∀ k, k ≤ n → ∑ i, N k i = (k : ℝ) := by
    intro k
    induction k with
    | zero => simp [hN0]
    | succ k ih =>
      intro hk
      rw [hN k (by omega)]
      simp only [Pi.add_apply, Finset.sum_add_distrib]
      rw [ih (by omega)]
      simp
  have hu : ∀ k, k ≤ n → ∀ i, N k i - P k i ≤ 1 := by
    intro k
    induction k with
    | zero => simp [hN0, hP0]
    | succ k ih =>
      intro hk i
      have hk' : k < n := by omega
      have hs : ∑ a, (P (k+1) a - N k a) = 1 := by
        rw [Finset.sum_sub_distrib, hPsum (k+1) hk, hNsum k (by omega)]
        push_cast
        ring
      have hbest : 0 ≤ P (k+1) (I (k+1)) - N k (I (k+1)) := by
        by_contra hh
        have hneg : P (k+1) (I (k+1)) - N k (I (k+1)) < 0 := lt_of_not_ge hh
        have hall : ∑ a, (P (k+1) a - N k a) ≤ 0 :=
          Finset.sum_nonpos (fun a _ => (hI k hk' a).trans hneg.le)
        linarith
      by_cases hi : i = I (k+1)
      · subst i
        rw [hN k hk']
        simp only [Pi.add_apply, Pi.single_eq_same]
        linarith
      · have hprev := ih (by omega) i
        have hpi := (hp (k+1) (by omega) hk).1 i
        rw [hN k hk', hPstep]
        simp only [Pi.add_apply, Pi.single_apply, if_neg hi, add_zero]
        linarith
  have hz : ∑ i, (N n i - P n i) = 0 := by
    rw [Finset.sum_sub_distrib, hNsum n le_rfl, hPsum n le_rfl, sub_self]
  intro i
  have hlow : -((K : ℝ)-1) ≤ N n i - P n i := by
    have he := Finset.sum_erase_add Finset.univ (fun a => N n a - P n a)
      (Finset.mem_univ i)
    have hbound : ∑ a ∈ Finset.univ.erase i, (N n a - P n a) ≤
        ∑ _a ∈ Finset.univ.erase i, (1 : ℝ) :=
      Finset.sum_le_sum (fun a _ => hu n le_rfl a)
    have hc : (∑ _a ∈ Finset.univ.erase i, (1 : ℝ)) = (K : ℝ)-1 := by
      simp [Finset.card_erase_of_mem, Nat.cast_sub (Nat.succ_le_of_lt hK)]
    rw [hc] at hbound
    rw [hz] at he
    linarith
  have hu' : N n i - P n i ≤ (K : ℝ)-1 := by
    by_cases hK1 : K = 1
    · subst K
      have hi : i = 0 := Subsingleton.elim _ _
      simpa [hi] using le_of_eq hz
    · have hk2 : (2 : ℝ) ≤ K := by exact_mod_cast (show 2 ≤ K by omega)
      linarith [hu n le_rfl i]
  exact abs_le.mpr ⟨hlow, hu'⟩
