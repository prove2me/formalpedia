-- Prove2me | solution 1 for ThreeSum.WeightedGlobalSignedPadding.padded_catalog_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:41:35.732982+00:00
-- url     : https://prove2.me/submissions/347d560c-6ad9-490d-a239-ac217d3c7e30

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_ThreeSum_TernarySignedReduction
import Definitions.Def_Submission_Weighted_Global_TernaryOversizeOverhead
import Definitions.Def_Submission_Weighted_Global_TernarySignedPadding
import Theorems.Thm_ThreeSum_WeightedGlobalSignedPadding_padded_carry_bound
import Theorems.Thm_ThreeSum_TernarySignedReduction_carryCatalog_card


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalSignedPadding
open Filter Real TernarySignedReduction WeightedGlobalCoverScale
open WeightedGlobalPrincipalDimensions WeightedGlobalOversizeOverhead WeightedGlobalOversizePrime
open WeightedGlobalEntropyRates WeightedGlobalLocalParameters WeightedGlobalOversizeRates WeightedGlobalParameters
open scoped Topology
namespace ThreeSum.WeightedGlobalSignedPadding
theorem _root_.solution {m b n U : ℕ} (hm : 0<m) (hb : 1<b) (hn : 1<n)
    {κ : ℝ} (hκ : 0≤κ) (hU : (U : ℝ)≤(n : ℝ)^κ) :
    ((carryCatalog (paddedLength b U (radixLength m n))).card : ℝ) ≤
      carryConstant b*(n : ℝ)^carryExponent m b κ := by
  have hh : ((carryCatalog (paddedLength b U (radixLength m n))).card : ℝ) ≤
      (2 : ℝ)^paddedLength b U (radixLength m n) := by
    exact_mod_cast carryCatalog_card (paddedLength b U (radixLength m n))
  exact hh.trans (padded_carry_bound hm hb hn hκ hU)
end ThreeSum.WeightedGlobalSignedPadding
