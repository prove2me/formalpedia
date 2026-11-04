-- Prove2me | solution 1 for ThreeSum.WeightedGlobalArenaMomentResources.source_homogeneous
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T17:29:16.612473+00:00
-- url     : https://prove2.me/submissions/5cf503be-b22d-4a26-8fc1-0093869e8e8c

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPairMass
import Definitions.Def_Submission_Weighted_Global_TernaryArenaReporterBounds
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceCertificate
import Definitions.Def_Submission_Weighted_Global_TernaryArenaQueryModel
import Definitions.Def_Submission_Weighted_Global_TernaryArenaMomentResources
import Theorems.Thm_ThreeSum_TernarySourceHostModel_mem_records
import Theorems.Thm_ThreeSum_WeightedGlobalArenaSourceCertificate_source_rank
import Theorems.Thm_ThreeSum_WeightedGlobalGoodOutputCatalog_mem_records
import Theorems.Thm_ThreeSum_WeightedSchedule_source_rank
attribute [local simp] ThreeSum.TernarySourceHostModel.mem_records
attribute [local simp] ThreeSum.WeightedGlobalGoodOutputCatalog.mem_records



set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaMomentResources
open Light WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup WeightedGlobalArenaPairMass
open WeightedGlobalCoverGoodMaps WeightedGlobalLocalParameters WeightedGlobalNativeMomentBounds
open WeightedGlobalMomentWeightBounds
variable {p m F r : ℕ} [Fact p.Prime]
namespace ThreeSum.WeightedGlobalArenaMomentResources
theorem _root_.solution (maps : Fin F→Weight m p) (cap : ℕ) (I : Input) (right : Bool) :
    ∀ pair∈(source (r := r) maps cap I right).records,
      WeightedGlobalBank.rank ((WeightedBankCanonical.enumeration (N m r) (cut m r)).word
        ((source (r := r) maps cap I right).key pair.2))=r*alphaRank m := by
  intro pair hp
  have hi := (TernarySourceHostModel.mem_records _ _ _ _ _ _).mp hp
  exact WeightedGlobalArenaSourceCertificate.source_rank maps cap I right pair.2 hi.2.1
end ThreeSum.WeightedGlobalArenaMomentResources
