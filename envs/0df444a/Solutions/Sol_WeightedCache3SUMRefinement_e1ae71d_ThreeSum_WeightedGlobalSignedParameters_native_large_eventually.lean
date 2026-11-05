-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalSignedParameters.native_large_eventually
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T11:40:04.514285+00:00
-- url     : https://prove2.me/submissions/9481876b-4deb-435a-9b7e-64e28b0bb6e5

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernarySignedPadding
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernarySignedParameters
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalSignedParameters_native_log_atTop

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalSignedParameters
open Filter Real WeightedGlobalSignedPadding WeightedGlobalCoverScale WeightedGlobalOversizeOverhead
open WeightedGlobalOversizePrime WeightedGlobalEntropyRates WeightedGlobalLocalParameters
open WeightedGlobalOversizeRates WeightedGlobalParameters
open scoped Topology
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalSignedParameters
theorem _root_.solution {K : ℕ} (hK : 0<K) (D : ℕ) :
    ∀ᶠ m : ℕ in atTop, D<nativePrime K m := by
  filter_upwards [(native_log_atTop hK).eventually_gt_atTop (D : ℝ)] with m hm
  have hlog := Real.log_le_self (Nat.cast_nonneg (nativePrime K m) : (0 : ℝ)≤_)
  exact_mod_cast hm.trans_le hlog
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalSignedParameters
