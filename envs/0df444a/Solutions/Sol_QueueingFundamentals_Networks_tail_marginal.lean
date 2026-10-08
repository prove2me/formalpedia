-- Prove2me | solution 1 for QueueingFundamentals.Networks.tail_marginal
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T03:12:10.084638+00:00
-- url     : https://prove2.me/submissions/eed2390b-25c1-455e-b272-8857a1f2d0f5

import Mathlib
import Definitions.Def_QueueingFundamentals_Networks_ClosedJackson

namespace TailMarginal1567

open QueueingFundamentals.Networks Finset

theorem mem_states_iff {k N : ℕ} (n : Fin k → ℕ) : n ∈ states k N ↔ ∑ j, n j = N := by
  unfold states
  simp only [Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨fun j => ?_, h⟩
    have : n j ≤ ∑ j, n j := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    omega

theorem sum_add_single {k : ℕ} (x : Fin k → ℕ) (i : Fin k) (m : ℕ) :
    ∑ j, (x + (Pi.single i m : Fin k → ℕ)) j = ∑ j, x j + m := by
  simp only [Pi.add_apply, Finset.sum_add_distrib]
  congr 1
  rw [Fintype.sum_eq_single i (fun j hj => by simp [hj])]
  simp

theorem prod_add_single {k : ℕ} (rho : Fin k → ℝ) (x : Fin k → ℕ) (i : Fin k) (m : ℕ) :
    ∏ j, rho j ^ (x + (Pi.single i m : Fin k → ℕ)) j = rho i ^ m * ∏ j, rho j ^ x j := by
  simp only [Pi.add_apply, pow_add, Finset.prod_mul_distrib]
  rw [mul_comm]
  congr 1
  rw [Fintype.prod_eq_single i (fun j hj => by simp [hj])]
  simp

theorem sub_add_single {k : ℕ} (n : Fin k → ℕ) (i : Fin k) (m : ℕ) (h : m ≤ n i) :
    n - (Pi.single i m : Fin k → ℕ) + Pi.single i m = n := by
  funext j
  by_cases hj : j = i
  · subst hj; simp; omega
  · simp [hj]

theorem key {k : ℕ} (rho : Fin k → ℝ) (N m : ℕ) (hm : m ≤ N) (i : Fin k) :
    ∑ n ∈ (states k N).filter (fun n => m ≤ n i), ∏ j, rho j ^ n j =
      rho i ^ m * ∑ n ∈ states k (N - m), ∏ j, rho j ^ n j := by
  rw [Finset.mul_sum]
  apply Finset.sum_nbij' (fun n => n - (Pi.single i m : Fin k → ℕ)) (fun n => n + (Pi.single i m : Fin k → ℕ))
  · intro n hn
    simp only [Finset.mem_filter, mem_states_iff] at hn ⊢
    have h1 := sum_add_single (n - Pi.single i m) i m
    rw [sub_add_single n i m hn.2] at h1
    omega
  · intro n hn
    simp only [Finset.mem_filter, mem_states_iff] at hn ⊢
    refine ⟨?_, ?_⟩
    · rw [sum_add_single, hn]; omega
    · simp
  · intro n hn
    simp only [Finset.mem_filter, mem_states_iff] at hn
    exact sub_add_single n i m hn.2
  · intro n _
    funext j
    simp
  · intro n hn
    simp only [Finset.mem_filter] at hn
    have h1 := prod_add_single rho (n - Pi.single i m) i m
    rw [sub_add_single n i m hn.2] at h1
    exact h1

end TailMarginal1567

open TailMarginal1567 in
open QueueingFundamentals.Networks in
theorem solution {k : ℕ} (rho : Fin k → ℝ) (hrho : ∀ i, 0 < rho i) (N m : ℕ) (hm : m ≤ N)
    (i : Fin k) :
    tailMarginal N (productForm (fun j n => rho j ^ n) N) i m =
      rho i ^ m * normConst (fun j n => rho j ^ n) (N - m) /
        normConst (fun j n => rho j ^ n) N := by
  unfold tailMarginal
  have h : ∀ n ∈ (states k N).filter (fun n => m ≤ n i),
      productForm (fun j n => rho j ^ n) N n =
        (∏ j, rho j ^ n j) / normConst (fun j n => rho j ^ n) N := by
    intro n hn
    simp only [Finset.mem_filter] at hn
    simp [productForm, hn.1]
  rw [Finset.sum_congr rfl h, ← Finset.sum_div, key rho N m hm i]
  rfl
