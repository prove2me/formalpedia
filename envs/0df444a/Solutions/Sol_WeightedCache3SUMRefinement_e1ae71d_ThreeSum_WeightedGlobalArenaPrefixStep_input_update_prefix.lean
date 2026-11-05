-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaPrefixStep.input_update_prefix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:39:40.085462+00:00
-- url     : https://prove2.me/submissions/5c5bbcac-91bb-43d1-81ca-36c2cfc04651

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaPrefixPotential
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaPrefixStep
import Theorems.Thm_Light_LocalsBut_update
import Theorems.Thm_Light_MatAt_congr
import Theorems.Thm_Light_Seg_congr
import Theorems.Thm_ThreeSum_LightKaratsuba_ProductAt_congr
import Theorems.Thm_ThreeSum_LightTernaryCountFrontend_row
import Theorems.Thm_ThreeSum_LightTernarySourceCountHost_Reads_update
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedCountFrontend_row
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedSourceCountHost_Reads_update
attribute [local simp] ThreeSum.LightTernaryCountFrontend.row
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedCountFrontend.row



set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaPrefixStep
open Finset TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps TernaryCoverLocal
open WeightedGlobalArenaSourceSetup WeightedGlobalArenaPrefixGroups WeightedGlobalArenaPrefixPairs WeightedGlobalArenaPrefixPotential
open WeightedGlobalNativePrefixLineage TernaryPairedPotential TernaryPairedContraction TernaryOriginalRowMenu
open TernaryExtensionEncoding
open scoped BigOperators
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 4000000
variable {p m F Λ : ℕ} [Fact p.Prime]
variable (maps : Fin F→Weight m p) (τ cap : ℕ) (I : Input) (L R : ℕ→Fin Λ→ℤ)
    (row : ℕ→(Fin Λ→ZMod p)→ₗ[ZMod p] ZMod p) (root : ℕ→ℕ→ZMod p)
    (Q : WeightedGlobalGoodOutputCatalog.Output m)
variable {E : Type*} [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod p) E]
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaPrefixStep
theorem _root_.solution (newrow : (Fin Λ→ZMod p)→ₗ[ZMod p] ZMod p)
    (newroot : ℕ→ZMod p) (r : ℕ) :
    input I L R (Function.update row r newrow) (fun o => Function.update (root o) r (newroot o)) r=
      input I L R row root r := by
  have hr (j : Fin r) : j.val≠r := Nat.ne_of_lt j.isLt
  have hL : (fun i => (coefficientCode (fun j : Fin r =>
      Function.update row r newrow j.val (fun t => (L i t : ZMod p))) : ℤ))=
      fun i => (coefficientCode (fun j : Fin r => row j.val (fun t => (L i t : ZMod p))) : ℤ) := by
    funext i
    congr 1
    congr 1
    funext j
    rw [Function.update_of_ne (hr j)]
  have hR : (fun i => (coefficientCode (fun j : Fin r =>
      Function.update row r newrow j.val (fun t => (R i t : ZMod p))) : ℤ))=
      fun i => (coefficientCode (fun j : Fin r => row j.val (fun t => (R i t : ZMod p))) : ℤ) := by
    funext i
    congr 1
    congr 1
    funext j
    rw [Function.update_of_ne (hr j)]
  have hO : (fun i => (coefficientCode (fun j : Fin r =>
      Function.update (root i) r (newroot i) j.val) : ℤ))=
      fun i => (coefficientCode (fun j : Fin r => root i j.val) : ℤ) := by
    funext i
    congr 1
    congr 1
    funext j
    rw [Function.update_of_ne (hr j)]
  unfold input
  rw [hL,hR,hO]
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaPrefixStep
