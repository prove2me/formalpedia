-- Prove2me | solution 1 for ThreeSum.WeightedGlobalArenaSourceCertificate.source_rank
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T17:17:42.942019+00:00
-- url     : https://prove2.me/submissions/d95f7938-24ac-41ea-8988-05b9d79fbd00

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceModel
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceCertificate
import Theorems.Thm_ThreeSum_WeightedGlobalArenaSourceCertificate_source_typed
import Theorems.Thm_ThreeSum_TernaryDimensionBounds_rank_eq_counts
import Theorems.Thm_ThreeSum_WeightedGlobalDimensionBounds_rank_eq_counts


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaSourceCertificate
open TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps
open WeightedGlobalArenaSourceSetup TernaryCanonicalDictionaries WeightedGlobalNativeCompleteFrontend
open LightTernarySourceHost TernaryCodeSemantics
variable {p m F r : ℕ} [Fact p.Prime]
set_option maxHeartbeats 3000000
namespace ThreeSum.WeightedGlobalArenaSourceCertificate
theorem _root_.solution (maps : Fin F→Weight m p) (cap : ℕ) (I : Input) (right : Bool)
    (j : ℕ) (hj : j<LightTernarySourceHost.size (source (r := r) maps cap I right).xs r) :
    WeightedGlobalBank.rank ((WeightedBankCanonical.enumeration (N m r) (cut m r)).word
      ((source (r := r) maps cap I right).key j))=r*alphaRank m := by
  rw [WeightedGlobalDimensionBounds.rank_eq_counts,source_typed maps cap I right j hj 1,
    source_typed maps cap I right j hj 2]
  unfold alphaRank
  ring
end ThreeSum.WeightedGlobalArenaSourceCertificate
