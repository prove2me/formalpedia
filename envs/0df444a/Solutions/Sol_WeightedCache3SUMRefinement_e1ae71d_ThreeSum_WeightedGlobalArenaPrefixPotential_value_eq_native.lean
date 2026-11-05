-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaPrefixPotential.value_eq_native
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:35:07.712912+00:00
-- url     : https://prove2.me/submissions/583af1ce-306b-419d-bebc-fdffe0d8a1df

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaPrefixPairs
import Definitions.Def_Submission_ThreeSum_TernaryPairedMinorReindex
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryNativeTensorScore
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaPrefixPotential
import Theorems.Thm_ThreeSum_LightTernaryCountFrontend_row
import Theorems.Thm_ThreeSum_TernaryPairedMinorReindex_paired_rowWeight
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedCountFrontend_row
attribute [local simp] ThreeSum.LightTernaryCountFrontend.row
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedCountFrontend.row



set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaPrefixPotential
open Finset TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps TernaryCoverLocal
open WeightedGlobalArenaSourceSetup WeightedGlobalArenaPrefixGroups WeightedGlobalArenaPrefixPairs
open WeightedGlobalNativePrefixLineage TernaryPairedPotential TernaryPairedContraction
open scoped BigOperators
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 4000000
variable {p m F Λ : ℕ} [Fact p.Prime]
variable (maps : Fin F→Weight m p) (τ cap : ℕ) (I : Input) (L R : ℕ→Fin Λ→ℤ)
    (row : ℕ→(Fin Λ→ZMod p)→ₗ[ZMod p] ZMod p) (root : ℕ→ℕ→ZMod p)
    (Q : WeightedGlobalGoodOutputCatalog.Output m)
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaPrefixPotential
theorem _root_.solution {J : ℕ} (maps : Fin F→Weight m p) (τ cap : ℕ) (I : Input)
    (A B : ℕ→ℕ→ℤ) (row : ℕ→(Fin (J+2)→ZMod p)→ₗ[ZMod p] ZMod p)
    (root : ℕ→ℕ→ZMod p) (Q : WeightedGlobalGoodOutputCatalog.Output m) (r K : ℕ) :
    value maps τ cap I (fun i t => A i t.val) (fun i t => B i t.val) row root Q r K=
      WeightedGlobalNativeTensorScore.pairedPotential
        (S (r := r) maps τ cap I (fun i t => A i t.val) (fun i t => B i t.val) row root Q) K J A B := by
  unfold value potential WeightedGlobalNativeTensorScore.pairedPotential
  rw [Fintype.sum_sigma]
  apply sum_congr rfl
  intro j hj
  apply sum_congr rfl
  intro e he
  rw [TernaryPairedMinorReindex.paired_rowWeight]
  rfl
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaPrefixPotential
