-- Prove2me | solution 1 for QEC.Coding.BDL26RXPhysicalStarTransport.two_run
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T17:14:55.696222+00:00
-- url     : https://prove2.me/submissions/6adbb088-5d64-4adb-81c1-e4508f90418a

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXFiniteBlockTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXPhysicalStarTransport
import Theorems.Thm_QEC_Coding_BDL26RXPhysicalStarTransport_parent_computed
import Theorems.Thm_QEC_Coding_BDL26RXPhysicalStarTransport_map1_with_potential
import Theorems.Thm_QEC_Coding_BDL26RXPhysicalStarTransport_lower_syndrome
import Theorems.Thm_QEC_Coding_BDL26RXPhysicalStarTransport_correction_difference_supported
import Theorems.Thm_QEC_Coding_BDL26RXPhysicalStarTransport_phi_supported
import Theorems.Thm_QEC_Coding_BDL26RXPhysicalStarTransport_lower_supported
import Theorems.Thm_QEC_Coding_BDL26RXPhysicalStarTransport_lower_weight
import Theorems.Thm_QEC_Coding_BDL26RXFiniteBlockTransport_correction_difference_supported
import Theorems.Thm_QEC_Coding_BDL26RXFiniteBlockTransport_lower_supported
import Theorems.Thm_QEC_Coding_BDL26RXFiniteBlockTransport_lower_syndrome
import Theorems.Thm_QEC_Coding_BDL26RXFiniteBlockTransport_map1_with_potential
import Theorems.Thm_QEC_Coding_BDL26RXFiniteBlockTransport_phi_supported
import Theorems.Thm_QEC_Coding_BDL26RXQBlockTransport_correction_difference_supported
import Theorems.Thm_QEC_Coding_BDL26RXQBlockTransport_lower_supported
import Theorems.Thm_QEC_Coding_BDL26RXQBlockTransport_lower_syndrome
import Theorems.Thm_QEC_Coding_BDL26RXQBlockTransport_map1_with_potential
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_correction_difference_supported
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_lower_supported
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_lower_syndrome
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_map1_with_potential
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXPhysicalStarTransport
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RXDecoderAdapter BDL26RXErrorPullback
open BDL26RZMap1CoordinateBridge BDL26RXXStarTransport
open BDL26RXLocalReplacement BDL26ReplacementSupport MultiscaleDecoder
open RXCoarseGraining RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (h : i.val % 2=0)
namespace QEC.Coding.BDL26RXPhysicalStarTransport
theorem _root_.solution (u : FamilyX S depth i.succ) (a b : Upper S depth i)
    (he : Localized S depth i u a b) :
    parent S (i.val+1) (Vertex.x u)=some (Vertex.x (parentX S depth i h u)) ∧
    ((indexedDecoderData S depth).selectedMap i).map1 (L S depth i h u a b)=
      updated S depth i h a b+(indexedFamily S depth).coboundary0 i.succ (Phi S depth i h u a b) ∧
    (indexedFamily S depth).coboundary1 i.castSucc (L S depth i h u a b)=
      (coarseSum S depth i h a b).val ∧
    hammingSupport ((run S depth i h a).correction+(run S depth i h b).correction) ⊆
      star1 S depth i h (parentX S depth i h u) ∧
    hammingSupport (Phi S depth i h u a b) ⊆ degreeZeroBlock S depth i h (parentX S depth i h u) ∧
    hammingSupport (L S depth i h u a b) ⊆
      physicalXStar (state S i.val).presentation (parentX S depth i h u) ∧
    HammingWeight (L S depth i h u a b) ≤ 7 := by
  exact ⟨parent_computed S depth i h u,map1_with_potential S depth i h u a b he,
    lower_syndrome S depth i h u a b he,correction_difference_supported S depth i h u a b he,
    phi_supported S depth i h u a b,lower_supported S depth i h u a b he,
    (lower_weight S depth i h u a b he).1.trans (lower_weight S depth i h u a b he).2⟩
end QEC.Coding.BDL26RXPhysicalStarTransport
