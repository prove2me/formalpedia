-- Prove2me | solution 1 for ThreeSum.WeightedGlobalArenaPrefixStep.input_update_prefix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T18:30:13.54075+00:00
-- url     : https://prove2.me/submissions/06a6cfed-780c-448a-8788-9e79fb6f395b

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPrefixPotential
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPrefixStep
import Theorems.Thm_Light_LocalsBut_update
import Theorems.Thm_Light_MatAt_congr
import Theorems.Thm_Light_Seg_congr
import Theorems.Thm_ThreeSum_LightKaratsuba_ProductAt_congr
import Theorems.Thm_ThreeSum_LightTernaryCountFrontend_row
import Theorems.Thm_ThreeSum_LightTernarySourceCountHost_Reads_update
import Theorems.Thm_ThreeSum_LightWeightedCountFrontend_row
import Theorems.Thm_ThreeSum_LightWeightedSourceCountHost_Reads_update
attribute [local simp] ThreeSum.LightTernaryCountFrontend.row
attribute [local simp] ThreeSum.LightWeightedCountFrontend.row



set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaPrefixStep
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
namespace ThreeSum.WeightedGlobalArenaPrefixStep
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
end ThreeSum.WeightedGlobalArenaPrefixStep
