-- Prove2me | solution 1 for ThreeSum.WeightedGlobalArenaQueryModel.setup_star_typed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T16:35:09.816625+00:00
-- url     : https://prove2.me/submissions/f30baccb-9d0b-4c18-b332-221a35ec8b00

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_ThreeSum_TernaryAddressDecode
import Definitions.Def_Submission_Weighted_Global_TernaryGoodOutputCatalog
import Definitions.Def_Submission_ThreeSum_TernaryWantedBatchProvenance
import Definitions.Def_Submission_Weighted_Global_TernaryCanonicalTupleCodes
import Definitions.Def_Submission_Weighted_Global_DimensionBounds
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceSetup
import Definitions.Def_Submission_Weighted_Global_TernaryArenaQueryModel
import Theorems.Thm_ThreeSum_WeightedGlobalRepeatedWords_canonical_typed


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaQueryModel
open TernaryJointType WeightedGlobalLocalParameters TernaryCoverLocal TernaryCoverHashes WeightedGlobalCoverGoodMaps
open TernaryWantedBatchIndex TernaryWantedBatchProvenance WeightedGlobalRepeatedWords
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 3000000
set_option maxRecDepth 18000
variable {m p F r : ℕ} [Fact p.Prime]
namespace ThreeSum.WeightedGlobalArenaQueryModel
theorem _root_.solution (maps : Fin F → Weight m p) (τ cap : ℕ)
    (localQ : WeightedGlobalGoodOutputCatalog.Output m) (I : WeightedGlobalArenaSourceSetup.Input) :
    HasType ((WeightedGlobalArenaSourceSetup.setup (r := r) maps τ cap localQ I).front.Qstar)
      (fun d => r*fixedPi m d) := by
  change HasType (canonical (fun _ : Fin r => localQ.val)) _
  apply canonical_typed
  intro i
  exact (Finset.mem_filter.mp localQ.property).2
end ThreeSum.WeightedGlobalArenaQueryModel
