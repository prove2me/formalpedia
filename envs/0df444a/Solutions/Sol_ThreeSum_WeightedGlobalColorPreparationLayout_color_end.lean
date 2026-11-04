-- Prove2me | solution 1 for ThreeSum.WeightedGlobalColorPreparationLayout.color_end
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T14:21:52.177206+00:00
-- url     : https://prove2.me/submissions/eec661dd-d011-474c-8279-693b0cce2acb

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryColorPreparation
import Definitions.Def_Submission_Weighted_Global_TernaryColorPreparationLayout
import Theorems.Thm_ThreeSum_LightTernaryColorPrelude_one_band


set_option autoImplicit false
open ThreeSum ThreeSum.WeightedGlobalColorPreparationLayout
open LightWeightedGlobalColorPreparation
set_option maxHeartbeats 1000000
namespace ThreeSum.WeightedGlobalColorPreparationLayout
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
end ThreeSum.WeightedGlobalColorPreparationLayout
