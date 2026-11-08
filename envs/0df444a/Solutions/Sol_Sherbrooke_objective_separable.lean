-- Prove2me | solution 1 for Sherbrooke.objective_separable
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T14:54:11.157825+00:00
-- url     : https://prove2.me/submissions/5ccc4e1d-3260-49ae-9bdf-e527c75179e0

import Mathlib
import Definitions.Def_Sherbrooke_objective

open Sherbrooke in
theorem solution {ι : Type*} [Fintype ι] (c : ι → ℝ) (Ξ : ι → ℕ → ℝ)
    (mbar : ι → ℕ)
    (hmin : ∀ i : ι, ∀ k : ℕ, c i * (mbar i : ℝ) + Ξ i (mbar i) ≤ c i * (k : ℝ) + Ξ i k) :
    ∀ m : ι → ℕ, Sherbrooke.objective c Ξ mbar ≤ Sherbrooke.objective c Ξ m := by
  intro m
  unfold Sherbrooke.objective
  exact Finset.sum_le_sum (fun i _ => hmin i (m i))
