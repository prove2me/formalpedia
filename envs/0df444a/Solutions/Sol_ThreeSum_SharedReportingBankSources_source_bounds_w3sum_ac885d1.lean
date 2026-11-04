-- Prove2me | solution 1 for ThreeSum.SharedReportingBankSources.source_bounds_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:20:38.594867+00:00
-- url     : https://prove2.me/submissions/8e7a6127-b0c5-4fdc-8302-826839b4c39d

import Definitions.Def_Submission_ThreeSum_SharedReportingBankSources
import Definitions.Def_Submission_ThreeSum_SourceBandFinite
import Definitions.Def_Submission_ThreeSum_SharedReportingBankSourceBounds
import Theorems.Thm_ThreeSum_LightBlockSourceBatchLayout_banks_le_work
import Theorems.Thm_ThreeSum_LightBlockSourceBatchLayout_masks_le_work
import Theorems.Thm_ThreeSum_LightBlockSourceBatchLayout_right_end_le_masks
import Theorems.Thm_ThreeSum_LightBlockSourceBatchLayout_right_ge_left
import Theorems.Thm_ThreeSum_SourceBandBankLayout_baseAt_mono
import Theorems.Thm_ThreeSum_SourceBandBankLayout_work_le_end


set_option autoImplicit false
open ThreeSum ThreeSum.SharedReportingBankSources
open Light SubsetAddress BlockIndexedQuery GlobalEncoding
namespace ThreeSum.SharedReportingBankSources
theorem _root_.solution {base NB NC g h J cut i s : ℕ}
    (hi : i < SourceBandPairSlices.count NB NC g)
    (hs : s < LightBlockSourceCatalog.count h J) :
    leftCell base h J cut i s < SourceBandBankData.finish base NB NC g h J cut ∧
    rightCell base h J cut i s < SourceBandBankData.finish base NB NC g h J cut ∧
    leftBase base h J cut i s+(J*(512*h)+1)*downsetCap (J*(512*h)) cut ≤
      SourceBandBankData.finish base NB NC g h J cut ∧
    rightBase base h J cut i s+(J*(512*h)+1)*downsetCap (J*(512*h)) cut ≤
      SourceBandBankData.finish base NB NC g h J cut := by
  have hend := SourceBandBankLayout.baseAt_mono (SourceBandBankData.first base) h J cut
    (show i+1 ≤ SourceBandPairSlices.count NB NC g by omega)
  have hwork := (SourceBandBankLayout.work_le_end (SourceBandBankData.first base) h J cut i).trans hend
  change LightBlockSourceBatchLayout.work (bankBase base h J cut i)
    (LightBlockSourceCatalog.count h J) (J*(512*h)) cut ≤
      SourceBandBankData.finish base NB NC g h J cut at hwork
  have hhead := LightBlockSourceBatchLayout.banks_le_work (bankBase base h J cut i)
    (LightBlockSourceCatalog.count h J) (J*(512*h)) cut
  unfold LightBlockSourceBatchLayout.banks at hhead
  have hright := (LightBlockSourceBatchLayout.right_end_le_masks
    (base := bankBase base h J cut i) (W := J*(512*h)) (cut := cut) hs).trans
    (LightBlockSourceBatchLayout.masks_le_work _ _ _ _)
  have hleft := LightBlockSourceBatchLayout.right_ge_left (bankBase base h J cut i)
    (LightBlockSourceCatalog.count h J) (J*(512*h)) cut s
  change leftBase base h J cut i s ≤ rightBase base h J cut i s at hleft
  change rightBase base h J cut i s+(J*(512*h)+1)*downsetCap (J*(512*h)) cut ≤
    LightBlockSourceBatchLayout.work (bankBase base h J cut i)
      (LightBlockSourceCatalog.count h J) (J*(512*h)) cut at hright
  unfold leftCell rightCell
  omega
end ThreeSum.SharedReportingBankSources
