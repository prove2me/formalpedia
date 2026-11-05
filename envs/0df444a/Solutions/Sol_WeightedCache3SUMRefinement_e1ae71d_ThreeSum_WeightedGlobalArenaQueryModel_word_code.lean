-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaQueryModel.word_code
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T14:11:08.681239+00:00
-- url     : https://prove2.me/submissions/6bebf013-a5e2-4fb0-a4da-508e5ccc5f62

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
import Theorems.Thm_Light_Seg_get
import Theorems.Thm_ThreeSum_TernaryWantedBatchProvenance_emit_decode
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalCanonicalTupleCodes_canonical_code
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalCanonicalTupleCodes_digit_cast
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalTupleWantedLookup_encode_digits


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
    (get (queries (r := r) maps τ targets positions n) j.val).2.1 =
      TernaryCodeSemantics.address (word maps τ targets positions n j) := by
  have he := emit_decode p (4^fixedLength m) F r (WeightedGlobalGoodOutputCatalog.raws maps τ)
    (WeightedGlobalGoodOutputCatalog.wordCodes maps τ) (WeightedGlobalGoodOutputCatalog.mapCodes maps τ) targets positions n j
  have hw := congrArg (fun e : Entry => e.2.1) he
  change TernaryWantedLittleEndian.encode (WeightedGlobalGoodOutputCatalog.wordCodes maps τ)
    (4^fixedLength m) 0 1 (descriptor maps τ targets positions n j).2 = _ at hw
  rw [WeightedGlobalTupleWantedLookup.encode_digits,zero_add,one_mul] at hw
  change Nat.ofDigits (4^fixedLength m)
    ((descriptor maps τ targets positions n j).2.map
      (fun i => (WeightedGlobalGoodOutputCatalog.wordCodes maps τ).getD i 0)) =
      (get (queries (r := r) maps τ targets positions n) j.val).2.1 at hw
  rw [←hw]
  apply Int.ofNat_inj.mp
  have hc := WeightedGlobalCanonicalTupleCodes.canonical_code
    (fun e : WeightedGlobalGoodOutputCatalog.Record m (Fin F) => e.2.val)
    (block maps τ targets positions n j)
  rw [WeightedGlobalCanonicalTupleCodes.digit_cast] at hc
  rw [block_map maps τ targets positions n j _ 0] at hc
  exact hc
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaQueryModel
