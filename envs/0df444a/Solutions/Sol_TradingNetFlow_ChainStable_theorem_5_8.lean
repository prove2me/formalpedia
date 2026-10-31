-- Prove2me | solution 1 for TradingNetFlow.ChainStable.theorem_5_8
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T10:35:01.191584+00:00
-- url     : https://prove2.me/submissions/73d8460e-2a4d-4b77-b475-82bba461a111
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_TradingNetFlow_ChainStable_Model
import Theorems.Thm_TradingNetFlow_ChainStable_contraction_mNaturalConcave
import Theorems.Thm_TradingNetFlow_ChainStable_theorem_4_1
import Theorems.Thm_TradingNetFlow_ChainStable_theorem_4_3
import Theorems.Thm_TradingNetFlow_ChainStable_corollary_5_6
import Theorems.Thm_TradingNetFlow_ChainStable_contraction_blockingChain_lift
import Theorems.Thm_TradingNetFlow_ChainStable_contraction_equilibrium_lift

open Finset TradingNetFlow.ChainStable

theorem solution {N E : Type*} [Fintype N] [DecidableEq N] [Fintype E] [DecidableEq E]
    (G : Economy N E) (hG : G.Standing) (X : Finset E) (pX : E → ℝ)
    (hX : G.IsChainStable X pX) :
    ∃ p : E → ℝ, G.IsCompetitiveEquilibrium X p ∧ ∀ e ∈ X, p e = pX e := by
  -- the contraction `G^X` satisfies the standing assumptions
  set H := G.contraction X pX with hH
  have hHs : H.Standing := by
    refine ⟨fun e => hG.1 e.1, fun i => ?_⟩
    exact contraction_mNaturalConcave G hG X pX i
  -- the no-trade outcome is efficient in `G^X`
  have heff : H.IsEfficient ∅ := by
    by_contra h
    -- a minimal welfare-improving set of trades
    obtain ⟨T, hT, hTmin⟩ := Finset.exists_min_image
      (univ.filter (fun T : Finset {e : E // e ∉ X} => H.welfare ∅ < H.welfare T)) Finset.card
      (by
        have : ∃ S, H.welfare ∅ < H.welfare S := by
          by_contra hc
          push_neg at hc
          exact h hc
        obtain ⟨S, hS⟩ := this
        exact ⟨S, by simp [hS]⟩)
    simp only [mem_filter, mem_univ, true_and] at hT hTmin
    have hmin : ∀ T' ⊂ T, ¬ H.welfare ∅ < H.welfare T' := by
      intro T' hT' hlt
      have := hTmin T' hlt
      have := Finset.card_lt_card hT'
      omega
    obtain ⟨-, pT, hblock⟩ := corollary_5_6 H hHs h T hT hmin
    exact hX.2 ⟨_, _, contraction_blockingChain_lift G X pX T pT hblock⟩
  obtain ⟨Y, q, hq⟩ := theorem_4_1 H hHs
  have hCE : H.IsCompetitiveEquilibrium ∅ q := theorem_4_3 H hHs Y ∅ q hq heff
  refine ⟨fun e => if h : e ∈ X then pX e else q ⟨e, h⟩,
    contraction_equilibrium_lift G X pX hX.1 q hCE, ?_⟩
  intro e he
  simp [he]
