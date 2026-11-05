-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalMomentWeightBounds.right_word_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T12:27:55.845288+00:00
-- url     : https://prove2.me/submissions/a2926178-4c68-4424-804e-e6681a430f65

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryNativeMomentBounds
import Mathlib.Data.Nat.Choose.Bounds
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryMomentWeightBounds

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalMomentWeightBounds
open LightWeightedGlobalMomentChannelFactory
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalMomentWeightBounds
theorem _root_.solution {U K k j : ℕ} (hk : k≤K) :
    max (U : ℤ) (2*((U : ℤ)+1)^(k-j))≤(rightWord U K : ℤ) := by
  have hp := pow_le_pow_right₀ (show (1 : ℤ)≤U+1 by omega) (show k-j≤K by omega)
  have hm := mul_le_mul_of_nonneg_left hp (by decide : (0 : ℤ)≤2)
  unfold rightWord
  push_cast
  apply max_le <;> nlinarith [show (0 : ℤ)≤2*((U : ℤ)+1)^K by positivity]
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalMomentWeightBounds
