-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalMomentWeightBounds.choose_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T12:27:57.863437+00:00
-- url     : https://prove2.me/submissions/d72e0b75-972f-4ddb-8033-eb8224b1a1da

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
theorem _root_.solution {k j K : ℕ} (hk : k≤K) : (k.choose j : ℤ)≤(2 : ℤ)^K := by
  have hc := (Nat.choose_le_two_pow k j).trans (Nat.pow_le_pow_right (by decide : 1≤2) hk)
  exact_mod_cast hc
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalMomentWeightBounds
