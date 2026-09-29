-- Prove2me | solution 1 for WorkbookCorrected.plus_65496
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T15:44:10.226682+00:00
-- url     : https://prove2.me/submissions/f05f3a9c-d6b2-4815-9d4f-6b36e17c15f7

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Filter
open scoped Topology

theorem solution (f : ℝ → ℝ) (hc : Continuous f) (hf : ∀ x : ℝ, 0 ≤ x → x < f x) (u : ℕ → ℝ) (u0 : u 0 = 0) (hu : ∀ n : ℕ, u (n+1)=f (u n)) : ∀ M : ℝ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → M < u n := by
  have hn : ∀ n : ℕ, 0 ≤ u n := by
    intro n
    induction n with
    | zero => rw [u0]
    | succ n ih => rw [hu n]; exact le_trans ih (le_of_lt (hf (u n) ih))
  have hm : StrictMono u := strictMono_nat_of_lt_succ (fun n => by rw [hu n]; exact hf (u n) (hn n))
  have ht : Tendsto u atTop atTop := by
    rcases tendsto_atTop_of_monotone hm.monotone with ht | ⟨l,hl⟩
    · exact ht
    · have hl0 : 0 ≤ l := ge_of_tendsto' hl hn
      have hfl : Tendsto (fun n => f (u n)) atTop (𝓝 (f l)) := hc.continuousAt.tendsto.comp hl
      have hshift : Tendsto (fun n => u (n+1)) atTop (𝓝 l) := hl.comp (tendsto_add_atTop_nat 1)
      have heq : f l=l := tendsto_nhds_unique hfl (by simpa only [hu] using hshift)
      have hlt := hf l hl0
      exact False.elim (by linarith)
  intro M
  have hh := (tendsto_atTop.1 ht) (M+1)
  obtain ⟨N,hN⟩ := eventually_atTop.1 hh
  exact ⟨N,fun n hn => lt_of_lt_of_le (by linarith) (hN n hn)⟩
example : (∀ (f : ℝ → ℝ) (hc : Continuous f) (hf : ∀ x : ℝ, 0 ≤ x → x < f x) (u : ℕ → ℝ) (u0 : u 0 = 0) (hu : ∀ n : ℕ, u (n+1)=f (u n)), ∀ M : ℝ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → M < u n) := @solution
#print axioms solution
