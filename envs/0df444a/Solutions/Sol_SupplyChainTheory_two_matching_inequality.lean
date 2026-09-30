-- Prove2me | solution 1 for SupplyChainTheory.two_matching_inequality
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-25T20:30:55.128482+00:00
-- url     : https://prove2.me/submissions/a568ecb9-b5b8-4636-a2b2-60005db644a8

import Mathlib
import Definitions.Def_SupplyChainTheory_tsp
import Theorems.Thm_SupplyChainTheory_comb_inequality

open Classical SupplyChainTheory

theorem solution {n s : ℕ} (hn : 3 ≤ n) (τ : Equiv.Perm (Fin n))
    (H : Finset (Fin n)) (T : Fin s → Finset (Fin n)) (hcomb : IsComb H T)
    (hteeth : ∀ k, (T k).card = 2) :
    edgesWithin τ H + ∑ k, edgesWithin τ (T k) ≤ H.card + (s - 1) / 2 := by
  -- A 2-matching configuration is a comb whose teeth have two nodes each.
  have h := comb_inequality hn τ H T hcomb
  have hsum : ∑ k, ((T k).card - 1) = s := by simp [hteeth]
  rw [hsum] at h
  obtain ⟨t, rfl⟩ := hcomb.2.2.2
  omega
