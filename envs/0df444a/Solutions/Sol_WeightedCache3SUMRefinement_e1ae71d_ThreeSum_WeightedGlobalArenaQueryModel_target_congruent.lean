-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaQueryModel.target_congruent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T14:11:09.547539+00:00
-- url     : https://prove2.me/submissions/f6c0dca5-bbbf-43de-b636-920a5b7b7729

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_ThreeSum_TernaryAddressDecode
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryGoodOutputCatalog
import Definitions.Def_Submission_ThreeSum_TernaryWantedBatchProvenance
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryCanonicalTupleCodes
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_DimensionBounds
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaSourceSetup
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaQueryModel
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaQueryModel_block_map
import Theorems.Thm_Light_Ends_block
import Theorems.Thm_ThreeSum_TernaryWantedBatchProvenance_decode_mem
import Theorems.Thm_ThreeSum_TernaryWantedBatchProvenance_mem_descriptors
import Theorems.Thm_ThreeSum_TernaryWantedRadix_mem_wantedOutputs
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalNativeTupleWitness_positional_map


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
    (positions : ℕ → ℕ) (n : ℕ) (j : Fin (queries (r := r) maps τ targets positions n).length) :
    (p : ℤ)^r ∣ targets (descriptor maps τ targets positions n j).1 -
      Radix.positionalHash (p : ℤ) (WeightedGlobalGoodOutputCatalog.key maps)
        (List.ofFn (block maps τ targets positions n j)) := by
  have hd := (mem_descriptors p r (WeightedGlobalGoodOutputCatalog.raws maps τ) targets n _).mp
    (decode_mem p (4^fixedLength m) F r (WeightedGlobalGoodOutputCatalog.raws maps τ)
      (WeightedGlobalGoodOutputCatalog.wordCodes maps τ) (WeightedGlobalGoodOutputCatalog.mapCodes maps τ) targets positions n j)
  have ho := (TernaryWantedRadix.mem_wantedOutputs (p : ℤ)
    (by exact_mod_cast (Fact.out : p.Prime).ne_zero) (WeightedGlobalGoodOutputCatalog.raws maps τ)
    r (targets _) _).mp hd.2
  have hm := block_map maps τ targets positions n j (WeightedGlobalGoodOutputCatalog.key maps) 0
  have he : Radix.positionalHash (p : ℤ)
      (fun k => (WeightedGlobalGoodOutputCatalog.raws maps τ).getD k 0)
      (descriptor maps τ targets positions n j).2 =
      Radix.positionalHash (p : ℤ) (WeightedGlobalGoodOutputCatalog.key maps)
        (List.ofFn (block maps τ targets positions n j)) := by
    calc
      _ = Radix.positionalHash (p : ℤ) id
          ((descriptor maps τ targets positions n j).2.map
            (fun k => (WeightedGlobalGoodOutputCatalog.raws maps τ).getD k 0)) :=
        WeightedGlobalNativeTupleWitness.positional_map _ _ id _
      _ = Radix.positionalHash (p : ℤ) id
          ((List.ofFn (block maps τ targets positions n j)).map (WeightedGlobalGoodOutputCatalog.key maps)) :=
        congrArg _ hm.symm
      _ = _ := (WeightedGlobalNativeTupleWitness.positional_map _ _ id _).symm
  rw [←he]
  exact ho.2.2
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaQueryModel
