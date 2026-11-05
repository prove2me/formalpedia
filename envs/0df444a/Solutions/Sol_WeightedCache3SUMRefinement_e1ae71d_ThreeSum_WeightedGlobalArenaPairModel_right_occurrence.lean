-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaPairModel.right_occurrence
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T14:52:53.100478+00:00
-- url     : https://prove2.me/submissions/306674ad-8916-4160-9564-f35142d62b15

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaSourceModel
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaQueryNative
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryNativePairMoments
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaPairModel
import Theorems.Thm_Light_Ends_block
import Theorems.Thm_Light_Seg_get
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaQueryModel_group_code
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaSourceModel_group_spec
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalNativeBlockPairs_occurrenceCode_injective


set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaPairModel
open Finset TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps WeightedGlobalArenaSourceSetup
open WeightedGlobalNativePairMoments WeightedGlobalArenaSourceModel TernaryCoverLocal
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 3000000
variable {p m F r : ℕ} [Fact p.Prime]
variable (maps : Fin F→Weight m p) (τ cap : ℕ) (localQ : WeightedGlobalGoodOutputCatalog.Output m) (I : Input)
variable {maps τ cap localQ I}
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaPairModel
theorem _root_.solution {i : ℕ} (hi : i<(Host (r := r) maps τ cap localQ I).front.count)
    (x : Pair (Host (r := r) maps τ cap localQ I) i) :
    (fun t => (WeightedGlobalCanonicalSourceBank.block true maps cap (rightIndex x) t).1)=
      (fun t => (outputBlock (maps := maps) (τ := τ) (cap := cap) (localQ := localQ) (I := I) hi t).1) := by
  apply WeightedGlobalNativeBlockPairs.occurrenceCode_injective
  have hg := (mem_filter.mp (mem_product.mp (mem_filter.mp x.property).1).2).2
  rw [←group_spec maps cap I true (rightIndex x)]
  change (source (r := r) maps cap I true).group x.val.2.2=_
  change (source (r := r) maps cap I true).group x.val.2.2=
    (TernaryWantedBatchIndex.get (entries (r := r) maps τ I) i).2.2 at hg
  rw [hg]
  exact WeightedGlobalArenaQueryModel.group_code maps τ I.targets I.positions I.requesterCount ⟨i,hi⟩
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaPairModel
