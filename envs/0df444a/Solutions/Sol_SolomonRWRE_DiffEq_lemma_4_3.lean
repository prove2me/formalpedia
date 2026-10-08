-- Prove2me | solution 1 for SolomonRWRE.DiffEq.lemma_4_3
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T02:18:00.048783+00:00
-- url     : https://prove2.me/submissions/f88d56cc-fcf9-4639-9afe-bda8d98b4390

import Mathlib
import Definitions.Def_SolomonRWRE_DiffEq_System

open MeasureTheory ProbabilityTheory Filter Topology
open SolomonRWRE.DiffEq

theorem solution {Ω : Type*} (σ : ℕ → Ω → ℝ) (n : ℕ) (hn : 1 ≤ n) (ω : Ω) :
    Z σ n ω = ∑ j ∈ Finset.Icc 1 n, ∏ i ∈ Finset.Icc j n, σ i ω := by
  have hall : ∀ n, Z σ n ω = ∑ j ∈ Finset.Icc 1 n, ∏ i ∈ Finset.Icc j n, σ i ω := by
    intro n
    induction n with
    | zero => simp [Z]
    | succ n ih =>
      rw [Z, ih, Finset.sum_Icc_succ_top (by omega)]
      simp only [Finset.Icc_self, Finset.prod_singleton]
      have he : (∑ j ∈ Finset.Icc 1 n, ∏ i ∈ Finset.Icc j (n + 1), σ i ω) =
          (∑ j ∈ Finset.Icc 1 n, ∏ i ∈ Finset.Icc j n, σ i ω) * σ (n + 1) ω := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j hj
        exact Finset.prod_Icc_succ_top (by have := (Finset.mem_Icc.mp hj).2; omega) _
      rw [he]
      ring
  exact hall n

#print axioms solution
