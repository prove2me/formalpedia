-- Prove2me | solution 1 for SupplyChainTheory.vcg_bidder_dominant
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-25T22:22:27.882352+00:00
-- url     : https://prove2.me/submissions/0b957921-0139-43d0-98ac-09c868fedf5c

import Mathlib
import Definitions.Def_SupplyChainTheory_auctions
import Theorems.Thm_SupplyChainTheory_vcg_core_lemma

open SupplyChainTheory

theorem solution {n : ℕ} (V : Finset (Fin (n + 1)) → ℝ) (hV : IsCoalitionalValue V) :
    (InCore V Finset.univ (vcgPayoff V Finset.univ) → BidderDominant V Finset.univ (vcgPayoff V Finset.univ))
      ∧ (¬ InCore V Finset.univ (vcgPayoff V Finset.univ) →
          (¬ ∃ π, BidderDominant V Finset.univ π)
          ∧ ∀ π, InCore V Finset.univ π → vcgPayoff V Finset.univ 0 < π 0) := by
  classical
  -- Lemma 15.1: bidder `k`'s VCG payoff is its largest payoff over the core.
  obtain ⟨-, hmax⟩ := vcg_core_lemma V hV
  have hle : ∀ π, InCore V Finset.univ π → ∀ k, k ≠ 0 → π k ≤ vcgPayoff V Finset.univ k :=
    fun π hπ k hk => (hmax k hk).2 ⟨π, hπ, rfl⟩
  -- A core vector matching the VCG payoffs of all bidders is the VCG vector.
  have hext : ∀ π, InCore V Finset.univ π → (∀ k, k ≠ 0 → π k = vcgPayoff V Finset.univ k) →
      π = vcgPayoff V Finset.univ := by
    intro π hπ hk
    funext i
    by_cases hi : i = 0
    · subst hi
      have hsum := hπ.1
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ 0)] at hsum
      have hrest : ∑ l ∈ Finset.univ.erase 0, π l
          = ∑ l ∈ Finset.univ.erase 0, (V Finset.univ - V (Finset.univ.erase l)) := by
        refine Finset.sum_congr rfl (fun l hl => ?_)
        rw [hk l (Finset.ne_of_mem_erase hl), vcgPayoff, if_neg (Finset.ne_of_mem_erase hl)]
      rw [vcgPayoff, if_pos rfl]
      linarith
    · exact hk i hi
  refine ⟨fun hin => ⟨hin, fun π' hπ' k _ hk => hle π' hπ' k hk⟩, fun hout => ⟨?_, ?_⟩⟩
  · -- A bidder-dominant vector would give every bidder its VCG payoff.
    rintro ⟨π, hπ, hdom⟩
    apply hout
    have : π = vcgPayoff V Finset.univ := by
      refine hext π hπ (fun k hk => le_antisymm (hle π hπ k hk) ?_)
      obtain ⟨⟨π', hπ', hπ'k⟩, -⟩ := hmax k hk
      rw [hπ'k]; exact hdom π' hπ' k (Finset.mem_univ k) hk
    exact this ▸ hπ
  · -- Each core vector underpays some bidder relative to VCG, so it pays the auctioneer more.
    intro π hπ
    have hgap : π 0 - vcgPayoff V Finset.univ 0
        = ∑ l ∈ Finset.univ.erase 0, (vcgPayoff V Finset.univ l - π l) := by
      have hsum := hπ.1
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ 0)] at hsum
      have hv : ∑ l ∈ Finset.univ.erase 0, vcgPayoff V Finset.univ l
          = ∑ l ∈ Finset.univ.erase 0, (V Finset.univ - V (Finset.univ.erase l)) :=
        Finset.sum_congr rfl (fun l hl => by rw [vcgPayoff, if_neg (Finset.ne_of_mem_erase hl)])
      rw [Finset.sum_sub_distrib, hv, vcgPayoff, if_pos rfl]
      linarith
    have hpos : 0 < ∑ l ∈ Finset.univ.erase 0, (vcgPayoff V Finset.univ l - π l) := by
      refine Finset.sum_pos' (fun l hl => sub_nonneg.mpr (hle π hπ l (Finset.ne_of_mem_erase hl)))
        ?_
      by_contra hno
      push Not at hno
      apply hout
      have : π = vcgPayoff V Finset.univ := hext π hπ (fun k hk => le_antisymm
        (hle π hπ k hk) (by linarith [hno k (Finset.mem_erase.mpr ⟨hk, Finset.mem_univ k⟩)]))
      exact this ▸ hπ
    linarith
