-- Prove2me | solution 1 for SupplyChainTheory.vcg_core_lemma
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-25T22:22:27.326052+00:00
-- url     : https://prove2.me/submissions/15ee857e-85c3-48e1-a7c8-9d1eae34140c

import Mathlib
import Definitions.Def_SupplyChainTheory_auctions

open SupplyChainTheory

theorem solution {n : ℕ} (V : Finset (Fin (n + 1)) → ℝ) (hV : IsCoalitionalValue V) :
    (∃ π, InCore V Finset.univ π)
      ∧ ∀ k : Fin (n + 1), k ≠ 0 →
        IsGreatest {x | ∃ π, InCore V Finset.univ π ∧ x = π k} (vcgPayoff V Finset.univ k) := by
  classical
  obtain ⟨hV0, hVmono⟩ := hV
  have hsingle : ∀ (i : Fin (n + 1)) (a : ℝ) (T : Finset (Fin (n + 1))),
      ∑ j ∈ T, Pi.single i a j = if i ∈ T then a else 0 := fun i a T =>
    Finset.sum_pi_single' i a T
  refine ⟨⟨Pi.single 0 (V Finset.univ), ?_, fun T _ => ?_⟩, fun k hk => ⟨?_, ?_⟩⟩
  · -- The auctioneer takes everything.
    rw [hsingle, if_pos (Finset.mem_univ _)]
  · rw [hsingle]
    split_ifs with h0
    · exact hVmono (Finset.subset_univ T)
    · rw [hV0 T h0]
  · -- Lemma 15.1's core vector: bidder `k` gets its VCG payoff, the auctioneer `V(N ∖ k)`.
    set b := V Finset.univ - V (Finset.univ.erase k) with hb
    have hb0 : 0 ≤ b := sub_nonneg.mpr (hVmono (Finset.erase_subset _ _))
    refine ⟨Pi.single 0 (V (Finset.univ.erase k)) + Pi.single k b, ⟨?_, fun T _ => ?_⟩, ?_⟩
    · simp only [Pi.add_apply, Finset.sum_add_distrib, hsingle, if_pos (Finset.mem_univ _), hb]
      ring
    · simp only [Pi.add_apply, Finset.sum_add_distrib, hsingle]
      by_cases h0 : (0 : Fin (n + 1)) ∈ T
      · rw [if_pos h0]
        by_cases hkT : k ∈ T
        · rw [if_pos hkT, hb, add_sub_cancel]; exact hVmono (Finset.subset_univ T)
        · rw [if_neg hkT, add_zero]
          exact hVmono (fun i hi => Finset.mem_erase.mpr ⟨fun h => hkT (h ▸ hi), Finset.mem_univ _⟩)
      · rw [if_neg h0, hV0 T h0, zero_add]
        split_ifs <;> linarith
    · simp only [Pi.add_apply, vcgPayoff, Pi.single_apply, if_neg hk, hb, zero_add, if_true]
  · -- Every core vector pays bidder `k` at most `V(N) − V(N ∖ k)`.
    rintro x ⟨π, ⟨hsum, hcore⟩, rfl⟩
    have h := hcore (Finset.univ.erase k) (Finset.erase_subset _ _)
    have hsplit := Finset.add_sum_erase Finset.univ π (Finset.mem_univ k)
    rw [vcgPayoff, if_neg hk]
    linarith
