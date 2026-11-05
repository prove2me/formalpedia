-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaSelectedSigned.input_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:44:40.925066+00:00
-- url     : https://prove2.me/submissions/5a11ed84-32e4-4037-ac28-98625bb12632

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaSelectedTerminal
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernarySignedFeatureHash
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaNativeComplete
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaSelectedSigned
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaSelectedSigned_selectedHash_raw
import Theorems.Thm_Light_MatAt_congr
import Theorems.Thm_Light_Seg_congr
import Theorems.Thm_ThreeSum_LightKaratsuba_ProductAt_congr


set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaSelectedSigned
open TernarySignedReduction TernarySignedLayout WeightedGlobalNativeRequesterCoverage
open WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate WeightedGlobalArenaSelectedBudgets
open WeightedGlobalArenaSelectedTerminal WeightedGlobalArenaBudgetExistence WeightedGlobalCoverGoodMaps
set_option maxHeartbeats 5000000
variable {p m F : ℕ} [Fact p.Prime]
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaSelectedSigned
theorem _root_.solution (I : Input) (A : Inputs) (s : State (p := p) A) (r U radix nA : ℕ)
    (X B C : ℕ→ℤ) :
    WeightedGlobalArenaSelectedTerminal.input (base I A.J nA) A s
      (left U radix A.J B) (right U radix A.J C) (requester U radix A.J X) r=
      WeightedGlobalArenaNativeComplete.input I U radix nA (selectedHash A s r) X B C := by
  have hL (j : ℕ) : sourceLeft (selectedHash A s r) U radix (B j)=
      hashMap A s r (fun t => (left U radix A.J B j t.val : ZMod p)) := selectedHash_raw A s r _
  have hR (j : ℕ) : sourceRight (selectedHash A s r) U radix (C j)=
      hashMap A s r (fun t => (right U radix A.J C j t.val : ZMod p)) := selectedHash_raw A s r _
  have hO (j : ℕ) : target (selectedHash A s r) U radix X j=
      (TernaryExtensionEncoding.coefficientCode
        (hashMap A s r (fun t => (requester U radix A.J X j t.val : ZMod p))) : ℤ) := by
    unfold target
    rw [selectedHash_raw]
    rfl
  unfold WeightedGlobalArenaSelectedTerminal.input WeightedGlobalArenaPrefixGroups.input base WeightedGlobalArenaNativeComplete.input
  congr 1
  · funext j
    rw [hL]
    rfl
  · funext j
    rw [hR]
    rfl
  · funext j
    rw [hO]
    rfl
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaSelectedSigned
