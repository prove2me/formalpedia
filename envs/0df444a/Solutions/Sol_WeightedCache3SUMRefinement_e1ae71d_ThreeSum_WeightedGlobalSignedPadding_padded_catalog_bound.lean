-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalSignedPadding.padded_catalog_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T11:41:15.114539+00:00
-- url     : https://prove2.me/submissions/2265a96a-7ac5-4bbb-8a10-41adf979ea3f

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_ThreeSum_TernarySignedReduction
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryOversizeOverhead
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernarySignedPadding
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalSignedPadding_padded_carry_bound
import Theorems.Thm_ThreeSum_TernarySignedReduction_carryCatalog_card


set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalSignedPadding
open Filter Real TernarySignedReduction WeightedGlobalCoverScale
open WeightedGlobalPrincipalDimensions WeightedGlobalOversizeOverhead WeightedGlobalOversizePrime
open WeightedGlobalEntropyRates WeightedGlobalLocalParameters WeightedGlobalOversizeRates WeightedGlobalParameters
open scoped Topology
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalSignedPadding
theorem _root_.solution {m b n U : ℕ} (hm : 0<m) (hb : 1<b) (hn : 1<n)
    {κ : ℝ} (hκ : 0≤κ) (hU : (U : ℝ)≤(n : ℝ)^κ) :
    ((carryCatalog (paddedLength b U (radixLength m n))).card : ℝ) ≤
      carryConstant b*(n : ℝ)^carryExponent m b κ := by
  have hh : ((carryCatalog (paddedLength b U (radixLength m n))).card : ℝ) ≤
      (2 : ℝ)^paddedLength b U (radixLength m n) := by
    exact_mod_cast carryCatalog_card (paddedLength b U (radixLength m n))
  exact hh.trans (padded_carry_bound hm hb hn hκ hU)
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalSignedPadding
