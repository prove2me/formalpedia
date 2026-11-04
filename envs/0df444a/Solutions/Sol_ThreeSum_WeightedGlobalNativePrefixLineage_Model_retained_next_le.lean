-- Prove2me | solution 1 for ThreeSum.WeightedGlobalNativePrefixLineage.Model.retained_next_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T15:46:30.74202+00:00
-- url     : https://prove2.me/submissions/e45f5603-c9a0-4e7e-bd59-8a7c09ae5285

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryNativePairedLineage
import Definitions.Def_Submission_Weighted_Global_TernaryNativePrefixLineage
import Theorems.Thm_ThreeSum_WeightedGlobalNativePrefixLineage_Model_lineage_injective
import Theorems.Thm_ThreeSum_WeightedGlobalNativePrefixLineage_Model_matrix_parent
import Theorems.Thm_ThreeSum_WeightedGlobalNativePrefixLineage_Model_last_row_event
import Theorems.Thm_ThreeSum_LightTernaryCountFrontend_row
import Theorems.Thm_ThreeSum_LightWeightedCountFrontend_row
import Theorems.Thm_ThreeSum_WeightedGlobalNativePairedLineage_retained_potential_le
attribute [local simp] ThreeSum.LightTernaryCountFrontend.row
attribute [local simp] ThreeSum.LightWeightedCountFrontend.row



set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalNativePrefixLineage
open Finset TernaryJointType TernaryCoverLocal TernaryCoverOutputCap
open TernaryOriginalRowMenu TernaryPairedPotential TernaryPairedContraction
open scoped BigOperators
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 3000000
variable {p Λ L F : ℕ} [Fact p.Prime] {α π : DigitType}
variable {O B C : Type*} [Fintype O] [Fintype B] [Fintype C]
open ThreeSum.WeightedGlobalNativePrefixLineage.Model
variable (M : Model p Λ L F α π O B C)
namespace ThreeSum.WeightedGlobalNativePrefixLineage.Model
theorem _root_.solution {r K : ℕ} {E : Type*} [Field E] [Fintype E]
    [DecidableEq E] [Algebra (ZMod p) E]
    (ℓ : E→ₗ[ZMod p] ZMod p) (seed : E×E) (hrow : M.row r=TernaryOriginalRowMenu.row Λ ℓ seed) :
    potential (M.matrix (r := r+1) (K := K))≤
      nextPotential (α := α) (π := π) ℓ (M.matrix (r := r) (K := K)) M.maps seed :=
  WeightedGlobalNativePairedLineage.retained_potential_le ℓ (M.matrix (r := r) (K := K))
    (M.matrix (r := r+1) (K := K)) M.maps seed M.lineage (M.lineage_injective r K)
    M.matrix_parent (M.last_row_event ℓ seed hrow)
end ThreeSum.WeightedGlobalNativePrefixLineage.Model
