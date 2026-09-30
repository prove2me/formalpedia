-- Prove2me | solution 1 for SupplyChainTheory.dualoc_gap
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-25T22:42:30.486451+00:00
-- url     : https://prove2.me/submissions/e58d8f8d-d9b9-4cef-b300-14f7f6f8eacc

import Mathlib
import Definitions.Def_SupplyChainTheory_location

open SupplyChainTheory


theorem solution {n m : ℕ} (chat : Fin n → Fin m → ℝ) (f : Fin m → ℝ) (v : Fin n → ℝ)
    (Jp : Finset (Fin m)) (a : Fin n → Fin m) (hPDP : PDP chat f v Jp) (ha : NearestIn chat Jp a) :
    (∑ j ∈ Jp, f j + ∑ i, chat i (a i)) - ∑ i, v i
      = ∑ i, ∑ j ∈ Jp.erase (a i), max 0 (v i - chat i j) := by
  obtain ⟨hPDP1, hPDP2⟩ := hPDP
  -- The nearest open site is within `vᵢ`.
  have hnear : ∀ i, chat i (a i) ≤ v i := by
    intro i
    obtain ⟨j, hj, hjv⟩ := hPDP2 i
    exact ((ha i).2 j hj).trans hjv
  -- PDP1: every open site's fixed cost is paid exactly by the customers' contributions.
  rw [← Finset.sum_congr rfl hPDP1, Finset.sum_comm]
  have hi : ∀ i, ∑ j ∈ Jp, max 0 (v i - chat i j)
      = (v i - chat i (a i)) + ∑ j ∈ Jp.erase (a i), max 0 (v i - chat i j) := by
    intro i
    rw [← Finset.add_sum_erase _ _ (ha i).1, max_eq_right (sub_nonneg.mpr (hnear i))]
  rw [Finset.sum_congr rfl (fun i _ => hi i), Finset.sum_add_distrib, Finset.sum_sub_distrib]
  ring
