-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.theorem_1_4
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T04:59:26.581845+00:00
-- url     : https://prove2.me/submissions/70fd50ce-1dad-45f1-a524-4bae69d08d35
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_ZeroFreeRRG_Hardcore_potts_positive_zero_free
import Theorems.Thm_ZeroFreeRRG_Hardcore_coloring_zero_free
open scoped Classical
open ZeroFreeRRG.Hardcore

theorem solution (d q : ℕ) (hd : 3 ≤ d) (hq : 2 ≤ q) :
    (∀ δ : ℝ, 0 < δ → δ < 1 - betaRSB d q →
      ∃ η : ℝ, 0 < η ∧
        PottsRapidMixing.WithHighProb d (fun n G =>
          ∀ β ∈ nbhd (realSegment (betaRSB d q + δ) 1) η, pottsZ q G β ≠ 0)) ∧
    (3 ≤ q → (d : EReal) < coloringDegreeRSB q →
      ∃ η : ℝ, 0 < η ∧
        PottsRapidMixing.WithHighProb d (fun n G =>
          ∀ β ∈ nbhd (realSegment 0 1) η, pottsZ q G β ≠ 0)) :=
  ⟨fun δ hδ hδmax => potts_positive_zero_free d q hd hq δ hδ hδmax,
   fun hq3 h => coloring_zero_free d q hd hq3 h⟩
