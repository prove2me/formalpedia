-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.infinityConjugationCorrectionSum_eq_sum_terms
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T13:20:20.009214+00:00
-- url     : https://prove2.me/submissions/c4a95b32-cde5-4794-bdf3-74ef1116aece

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingStabilizer
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityAction

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ)
    (k bound : ℕ) (ζ : ConstantExtension P r) :
    infinityConjugationCorrectionSum P r u k bound ζ =
      ∑ i ∈ Finset.range bound, infinityCorrectionTerm P r u k i ζ :=
  rfl
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
