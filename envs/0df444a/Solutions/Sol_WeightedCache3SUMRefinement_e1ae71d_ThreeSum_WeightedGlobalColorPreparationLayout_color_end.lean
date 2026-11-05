-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalColorPreparationLayout.color_end
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T11:49:27.043701+00:00
-- url     : https://prove2.me/submissions/cb816bed-07ba-42f3-9468-b678f1b31be0

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryColorPreparation
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryColorPreparationLayout
import Theorems.Thm_ThreeSum_LightTernaryColorPrelude_one_band


set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalColorPreparationLayout
open LightWeightedGlobalColorPreparation
set_option maxHeartbeats 1000000
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalColorPreparationLayout
theorem _root_.solution {free n W : ℕ} (hn : 0<n) (hW : LightColorParametersCosts.width n≤W) :
    LightTernaryColorPrelude.space free n≤headerAt free n W := by
  obtain ⟨_,hc,hw⟩ := LightTernaryColorPrelude.one_band hn
  unfold LightTernaryColorPrelude.space LightColorBands.space ColorBandBounds.space
  rw [hc,hw]
  unfold LightTernaryColorPrelude.work LightTernaryColorPrelude.ce LightTernaryColorPrelude.cv
    LightTernaryColorPrelude.be LightTernaryColorPrelude.bv LightTernaryColorPrelude.ae
    LightTernaryColorPrelude.av LightTernaryColorPrelude.class2 LightTernaryColorPrelude.class1
    LightTernaryColorPrelude.class0 headerAt
  omega
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalColorPreparationLayout
