-- Prove2me | solution 1 for QEC.Coding.BDL26RZPhysicalXStarTransport.upperStar_subset_inputBlocks
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T16:53:06.94317+00:00
-- url     : https://prove2.me/submissions/fe3f5a56-7e9b-4f28-872e-1930ea446a80

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXPhysicalStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Snapshots
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalXStarTransport
import Theorems.Thm_QEC_Coding_BDL26RZPhysicalXStarTransport_raw_star_cover
import Theorems.Thm_QEC_Coding_BDL26RZPhysicalXStarTransport_actual_incidence
import Theorems.Thm_QEC_Coding_BDL26RXPhysicalStarTransport_mem_physicalXStar
import Theorems.Thm_QEC_Coding_BDL26RZPhysicalStarTransport_actual_incidence
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm
attribute [local simp] QEC.Coding.BDL26RXPhysicalStarTransport.mem_physicalXStar



set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RZPhysicalXStarTransport
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26DecodingGraph BDL26IndexedDecoder BDL26RZLocalReplacement
open BDL26RZMap1CoordinateBridge BDL26ReplacementSupport BDL26LevelTwoDistance
open BDL26ReplacementCochainMaps BDL26RZDecoderAdapter BDL26RZErrorPullback
open BDL26RZFiniteBlockTransport MultiscaleDecoder
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (odd : ¬i.val%2=0)
namespace QEC.Coding.BDL26RZPhysicalXStarTransport
theorem _root_.solution (u : FamilyX S depth i.succ) :
    upperStar S depth i u ⊆ inputBlocks S depth i odd (Q0 S depth i odd u) (Z0 S depth i odd u) := by
  intro r hr
  have hi := (actual_incidence S depth i odd u r).symm.trans
    ((BDL26RXPhysicalStarTransport.mem_physicalXStar _ _ _).mp hr)
  apply Finset.mem_union.mpr
  have h := raw_star_cover (Old S depth i) (state S i.val).admissible.toTannerSquareAdmissible S
    (coord0 S depth i odd u) (coord1 S depth i odd r) hi
  rcases Finset.mem_union.mp h with hq | hz
  · exact Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hq⟩)
  · exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hz⟩)
end QEC.Coding.BDL26RZPhysicalXStarTransport
