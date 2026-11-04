-- Prove2me | solution 1 for ThreeSum.WeightedGlobalArenaSourceModel.key_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T16:54:33.887529+00:00
-- url     : https://prove2.me/submissions/72da1481-65fb-4bcb-92a8-1ef577fcab69

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceSetup
import Definitions.Def_Submission_Weighted_Global_TernaryCanonicalSourceBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceModel
import Theorems.Thm_ThreeSum_WeightedGlobalCanonicalSourceBank_source_index_spec


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaSourceModel
open TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps WeightedGlobalArenaSourceSetup
open TernaryCanonicalDictionaries WeightedGlobalNativeCompleteFrontend
attribute [local instance] Classical.propDecidable
variable {p m F r : ℕ} [Fact p.Prime]
namespace ThreeSum.WeightedGlobalArenaSourceModel
theorem _root_.solution (maps : Fin F→Weight m p) (cap : ℕ) (I : Input) (right : Bool)
    (j : Index (r := r) maps cap right) :
    (source (r := r) maps cap I right).key j.val<(source (r := r) maps cap I right).bank :=
  (WeightedGlobalCanonicalSourceBank.source_index_spec right maps cap j).1
end ThreeSum.WeightedGlobalArenaSourceModel
