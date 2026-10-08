-- Prove2me | solution 1 for SuttonTD.Convergence.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T05:30:55.443979+00:00
-- url     : https://prove2.me/submissions/875e74b2-5918-4691-a83d-7448cdb27a2e

import Mathlib
import Definitions.Def_SuttonTD_Convergence_PerSequenceChanges

set_option autoImplicit false

theorem sutton1f817bd9_telescope {V : Type*} [AddCommGroup V] [Module ℝ V]
    (c : ℝ) (f : ℕ → ℝ) (x : ℕ → V) (n : ℕ) :
    ∑ t ∈ Finset.range n, (c * (f (t + 1) - f t)) • ∑ k ∈ Finset.range (t + 1), x k =
      ∑ k ∈ Finset.range n, (c * (f n - f k)) • x k := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, Finset.smul_sum,
      Finset.sum_range_succ (fun k => (c * (f (n + 1) - f k)) • x k),
      Finset.sum_range_succ (fun k => (c * (f (n + 1) - f n)) • x k), ← add_assoc,
      ← Finset.sum_add_distrib]
    congr 1
    · apply Finset.sum_congr rfl
      intro k _
      rw [← add_smul]
      congr 1
      ring

open SuttonTD.Convergence in
theorem solution {K : ℕ} (m : ℕ) (xs : ℕ → Fin K → ℝ) (z α : ℝ) (w : Fin K → ℝ) :
    widrowHoffChange m xs z α w = tdOneChange m xs z α w := by
  unfold tdOneChange widrowHoffChange
  rw [sutton1f817bd9_telescope α (linearPrediction m xs z w) xs m]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k < m := Finset.mem_range.mp hk
  simp [linearPrediction, hk']
