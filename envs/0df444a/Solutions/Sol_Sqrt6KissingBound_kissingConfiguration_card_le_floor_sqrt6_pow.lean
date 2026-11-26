-- Prove2me | solution 1 for Sqrt6KissingBound.kissingConfiguration_card_le_floor_sqrt6_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:35:45.910552+00:00
-- url     : https://prove2.me/submissions/abee0fa5-c55f-4ea1-b2a6-efb67bc51c4d

import Definitions.Def_Sqrt6KissingBound_DimensionOne
import Definitions.Def_Sqrt6KissingBound_DimensionThree
import Definitions.Def_Sqrt6KissingBound_DimensionFour
import Definitions.Def_Sqrt6KissingBound_BiconeBounds
import Definitions.Def_Sqrt6KissingBound_KissingBound
import Theorems.Thm_Sqrt6KissingBound_kissingConfiguration_card_le_sqrt6_pow

set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
namespace Sqrt6KissingBound
theorem _root_.solution {n : ℕ} (hn : 1 ≤ n)
    (X : Finset (EuclideanSpace ℝ (Fin n)))
    (hX : IsKissingConfiguration X) :
    X.card ≤ ⌊(Real.sqrt 6) ^ n⌋₊ := by
  exact Nat.le_floor (kissingConfiguration_card_le_sqrt6_pow hn X hX)
end Sqrt6KissingBound
