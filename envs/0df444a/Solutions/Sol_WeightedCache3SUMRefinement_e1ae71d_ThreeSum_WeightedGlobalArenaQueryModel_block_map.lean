-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaQueryModel.block_map
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T13:59:42.148707+00:00
-- url     : https://prove2.me/submissions/c9238cd9-eeca-4d3c-bae1-b0d85aab76a3

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaQueryModel

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
    (positions : ℕ → ℕ) (n : ℕ) (j : Fin (queries (r := r) maps τ targets positions n).length)
    {A : Type*} (f : WeightedGlobalGoodOutputCatalog.Record m (Fin F) → A) (fallback : A) :
    (List.ofFn (block maps τ targets positions n j)).map f =
      (descriptor maps τ targets positions n j).2.map
        (fun k => ((WeightedGlobalGoodOutputCatalog.records maps τ).map f).getD k fallback) := by
  have hd := descriptor_spec maps τ targets positions n j
  apply List.ext_getElem (by simp [hd.2.1])
  intro i hi hi'
  have hiR : i < r := by simpa using hi
  have hiD : i < (descriptor maps τ targets positions n j).2.length := by omega
  have hk := hd.2.2 _ (List.getElem_mem hiD)
  simp only [List.getElem_map,List.getElem_ofFn,block]
  rw [List.getD_eq_getElem _ _ (by simpa using hk),List.getElem_map]
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaQueryModel
