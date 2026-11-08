-- Prove2me | solution 1 for PCNonBool.observation_5_15
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T04:19:05.195744+00:00
-- url     : https://prove2.me/submissions/2e0aee2b-44ce-4184-9aae-451dcecad166

import Mathlib
import Definitions.Def_PCNonBool_BipGraph
import Definitions.Def_PCNonBool_boundaryOn
import Definitions.Def_PCNonBool_IsBoundaryExpander

open PCNonBool in
theorem solution {U V : Type*} [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V]
    (G : BipGraph U V) (s Δ : ℕ) (c ν : ℝ) (hG : IsBoundaryExpander G s Δ c) (hν : ν < c)
    (W : Finset V) (hW : W.card ≤ Δ * s) (X : Finset U) (hX : X.card ≤ s)
    (hXW : ((boundaryOn G Finset.univ X \ W).card : ℝ) ≤ ν * X.card) :
    (X.card : ℝ) ≤ W.card / (c - ν) := by
  have h1 : c * (X.card : ℝ) ≤ ((boundaryOn G Finset.univ X).card : ℝ) :=
    hG.2 X (Finset.subset_univ X) hX
  have h2 : ((boundaryOn G Finset.univ X).card : ℝ) ≤
      ((boundaryOn G Finset.univ X \ W).card : ℝ) + (W.card : ℝ) := by
    exact_mod_cast Finset.card_le_card_sdiff_add_card
  rw [le_div_iff₀ (by linarith)]
  nlinarith
