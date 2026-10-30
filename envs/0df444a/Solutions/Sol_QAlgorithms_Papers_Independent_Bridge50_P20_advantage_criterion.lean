-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Bridge50.P20.advantage_criterion
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T15:10:22.919369+00:00
-- url     : https://prove2.me/submissions/f1a545d7-eecd-45dd-85fd-4f593d7fc06c

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P20
noncomputable section

namespace QAlgorithms.Papers.Independent.Bridge50.P20

open QAlgorithms QAlgorithms.Entanglement

-- Reuse pinned accepted definitions; source-specific conventions are audited below.

open QAlgorithms.Papers.Independent.Dependency50.P35 (maxRelative)

open QAlgorithms.Papers.Independent.Information100.P04 (bellProjector)

open QAlgorithms.Papers.Independent.Information100.P53 (amplitudeDamping)

open QAlgorithms.Papers.Independent.Information100.P75 (mixedIdentity)

open QAlgorithms.Papers.Independent.Next46.P29 (zRotation)

open QAlgorithms.Papers.Independent.Support50.P11 (choiState)

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

end QAlgorithms.Papers.Independent.Bridge50.P20

open QAlgorithms.Papers.Independent.Bridge50.P20 in
theorem solution (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hsum : 0 < a + b) :
    (-1 ≤ relativeAdvantage a b ∧ relativeAdvantage a b ≤ 1) ∧
      (0 < relativeAdvantage a b ↔ b < a) := by
  unfold relativeAdvantage
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [le_div_iff₀ hsum]; linarith
  · rw [div_le_iff₀ hsum]; linarith
  · rw [div_pos_iff_of_pos_right hsum, sub_pos]

end
