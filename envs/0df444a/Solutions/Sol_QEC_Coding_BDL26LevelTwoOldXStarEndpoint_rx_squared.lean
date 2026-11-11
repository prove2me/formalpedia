-- Prove2me | solution 1 for QEC.Coding.BDL26LevelTwoOldXStarEndpoint.rx_squared
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T19:57:33.201584+00:00
-- url     : https://prove2.me/submissions/97fda9bf-3a12-48d9-ab43-526329c1c7c7

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDecoder
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalXStarTransport
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoOldXStarEndpoint
import Theorems.Thm_QEC_Coding_BDL26LevelTwoDistance_tannerCoboundary_squared
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
theorem _root_.solution (S : OddScale) (u : V1 S) :
    rxCoboundary1 Seed S (rxCoboundary0 Seed S u)=0 := by
  have h := LinearMap.congr_fun (tannerCoboundary_squared (P S)) u
  change tannerCoboundary1 (rxReplacementPresentation Seed S)
    (tannerCoboundary0 (rxReplacementPresentation Seed S) u)=0 at h
  rw [rxPresentation_coboundary0_eq Seed baseTannerSquareAdmissibleV4
    baseTannerSquareCellularRegular S,
    rxPresentation_coboundary1_eq Seed baseTannerSquareAdmissibleV4
    baseTannerSquareCellularRegular S] at h
  exact h
end QEC.Coding.BDL26LevelTwoOldXStarEndpoint
