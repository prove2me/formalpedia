-- Prove2me | solution 1 for UniformCounting.uniformProbability_mono
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-26T15:18:55.533868+00:00
-- url     : https://prove2.me/submissions/77dc225c-c695-4b43-acde-32edb8aa2ba6

import Mathlib
import Definitions.Def_OnlineStochMatching_SuggestedMatching_BallsInBins

set_option autoImplicit false

-- carved from submission 4a5e26af-423d-4e99-b667-4dcd719297c2, lines 1133-1142

theorem solution {Ω : Type} [Fintype Ω] (P Q : Ω → Prop)
    (h : ∀ ω, P ω → Q ω) :
    OnlineStochMatching.SuggestedMatching.uniformProbability P ≤
      OnlineStochMatching.SuggestedMatching.uniformProbability Q := by
  classical
  unfold OnlineStochMatching.SuggestedMatching.uniformProbability
  rcases Nat.eq_zero_or_pos (Fintype.card Ω) with h0 | hpos
  · simp [h0]
  · have hC : (0 : ℝ) < Fintype.card Ω := by exact_mod_cast hpos
    apply div_le_div_of_nonneg_right _ hC.le
    exact_mod_cast Finset.card_le_card (fun ω hω => by
      simp only [Finset.mem_filter] at hω ⊢; exact ⟨hω.1, h ω hω.2⟩)
