-- Prove2me | solution 1 for PLCMarkets.ExactCover.exactCover_iff_equilibrium
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-08T02:57:25.991632+00:00
-- url     : https://prove2.me/submissions/5d090ea5-2021-4e84-8781-5958e17609c9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_PLCMarkets_ExactCover_X3C
import Definitions.Def_PLCMarkets_ExactCover_MarketD
import Theorems.Thm_PLCMarkets_ExactCover_lemma_8_2_equilibrium_of_exactCover
import Theorems.Thm_PLCMarkets_ExactCover_lemma_8_3_exactCover_of_approxEquilibrium

theorem solution (n : ℕ) (C : Fin n → Finset (Fin n))
    (hcard : ∀ i, (C i).card = 3) (hdiv : 3 ∣ n) (hn : 35 < n)
    (hcover : ∀ x : Fin n, ∃ i, x ∈ C i) :
    (PLCMarkets.ExactCover.HasExactCover C ↔ ∃ p : PLCMarkets.ExactCover.Good n → ℝ, (PLCMarkets.ExactCover.marketD C).IsEquilibrium p) ∧
      (PLCMarkets.ExactCover.HasExactCover C ↔
        ∃ p : PLCMarkets.ExactCover.Good n → ℝ, (PLCMarkets.ExactCover.marketD C).IsApproxEquilibrium (((n : ℝ) ^ 5)⁻¹) p) := by
  have toApprox : ∀ p, (PLCMarkets.ExactCover.marketD C).IsEquilibrium p →
      (PLCMarkets.ExactCover.marketD C).IsApproxEquilibrium (((n : ℝ) ^ 5)⁻¹) p := by
    rintro p ⟨hs, x, hx, hc⟩
    refine ⟨hs, x, hx, fun j => ?_⟩
    rw [hc j, sub_self, abs_zero]
    unfold PLCMarkets.ExactCover.ADMarket.supply
    exact mul_nonneg (by positivity)
      (Finset.sum_nonneg fun i _ => by exact_mod_cast (PLCMarkets.ExactCover.marketD C).endow_nonneg i j)
  have fwd := PLCMarkets.ExactCover.lemma_8_2_equilibrium_of_exactCover n C hcard hdiv hn hcover
  have bwd := fun h => PLCMarkets.ExactCover.lemma_8_3_exactCover_of_approxEquilibrium n C hcard hdiv hn hcover h
  refine ⟨⟨fwd, fun h => bwd (Or.inl h)⟩, ⟨fun h => ?_, fun h => bwd (Or.inr h)⟩⟩
  obtain ⟨p, hp⟩ := fwd h
  exact ⟨p, toApprox p hp⟩
