-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaQueryModel.owner_blocks_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T13:32:13.199303+00:00
-- url     : https://prove2.me/submissions/243f3030-b92b-4e0a-b188-ece2202c91a0

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_ThreeSum_TernaryAddressDecode
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryGoodOutputCatalog
import Definitions.Def_Submission_ThreeSum_TernaryWantedBatchProvenance
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryCanonicalTupleCodes
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_DimensionBounds
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaSourceSetup
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaQueryModel
import Theorems.Thm_Light_Ends_block
import Theorems.Thm_ThreeSum_TernaryWantedBatchProvenance_decode_injective


set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaQueryModel
open TernaryJointType WeightedGlobalLocalParameters TernaryCoverLocal TernaryCoverHashes WeightedGlobalCoverGoodMaps
open TernaryWantedBatchIndex TernaryWantedBatchProvenance WeightedGlobalRepeatedWords
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 3000000
set_option maxRecDepth 18000
variable {m p F r : ℕ} [Fact p.Prime]
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaQueryModel
theorem _root_.solution (maps : Fin F → Weight m p) (τ : ℕ) (targets : ℕ → ℤ)
    (positions : ℕ → ℕ) (n : ℕ) :
    Function.Injective (fun j : Fin (queries (r := r) maps τ targets positions n).length =>
      ((descriptor maps τ targets positions n j).1,block maps τ targets positions n j)) := by
  intro a b hab
  apply decode_injective p (4^fixedLength m) F r (WeightedGlobalGoodOutputCatalog.raws maps τ)
    (WeightedGlobalGoodOutputCatalog.wordCodes maps τ) (WeightedGlobalGoodOutputCatalog.mapCodes maps τ) targets positions n
  change descriptor maps τ targets positions n a = descriptor maps τ targets positions n b
  apply Prod.ext
  · exact congrArg (fun x : ℕ × (Fin r → WeightedGlobalGoodOutputCatalog.Record m (Fin F)) => x.1) hab
  · have ha := descriptor_spec maps τ targets positions n a
    have hb := descriptor_spec maps τ targets positions n b
    apply List.ext_getElem (by omega)
    intro i hi hj
    have hir : i < r := by omega
    have hblock := congrFun (congrArg (fun x : ℕ × (Fin r → WeightedGlobalGoodOutputCatalog.Record m (Fin F)) => x.2) hab) ⟨i,hir⟩
    have hn : (WeightedGlobalGoodOutputCatalog.records maps τ).Nodup :=
      (WeightedGlobalGoodOutputCatalog.catalog maps τ).nodup_toList
    exact hn.getElem_inj_iff.mp hblock
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaQueryModel
