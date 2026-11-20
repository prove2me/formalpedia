-- Prove2me | solution 1 for QEC.Coding.BDL26LevelTwoOldXStarEndpoint.actual_neighborhood_relative_exact
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:55:04.745071+00:00
-- url     : https://prove2.me/submissions/fc58542f-a69b-47d0-a7ae-200e45548e67

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDecoder
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalXStarTransport
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoOldXStarEndpoint
import Theorems.Thm_QEC_Coding_BDL26LevelTwoOldXStarEndpoint_neighborhood_relative_exact
import Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_rxPresentation_coboundary0_eq
import Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_rxPresentation_coboundary1_eq


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26LevelTwoOldXStarEndpoint
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26RZLocalReplacement BDL26RZMap1CoordinateBridge
open BDL26ReplacementCochainMaps BDL26LevelTwoCode BDL26LevelTwoDistance
open BDL26LevelTwoDecoder BDL26DecodingGraph
open scoped Classical BigOperators
namespace QEC.Coding.BDL26LevelTwoOldXStarEndpoint
theorem _root_.solution (S : OddScale) (x : BaseX)
    (w : Word F (P S).Q) (hc : tannerCoboundary1 (P S) w=0)
    (a b : (P S).Q)
    (hw : ∀ r, w r≠0 → r∈Neighborhood S x ∨ r=a ∨ r=b) :
    ∃ g : Word F (P S).X, tannerCoboundary0 (P S) g=w := by
  change tannerCoboundary1 (rxReplacementPresentation Seed S) w=0 at hc
  rw [rxPresentation_coboundary1_eq Seed baseTannerSquareAdmissibleV4
    baseTannerSquareCellularRegular S] at hc
  obtain ⟨g,hg⟩ := neighborhood_relative_exact S x w hc a b hw
  refine ⟨g,?_⟩
  change tannerCoboundary0 (rxReplacementPresentation Seed S) g=w
  rw [rxPresentation_coboundary0_eq Seed baseTannerSquareAdmissibleV4
    baseTannerSquareCellularRegular S]
  exact hg
end QEC.Coding.BDL26LevelTwoOldXStarEndpoint
