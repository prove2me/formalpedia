-- Prove2me | solution 1 for QEC.Coding.BDL26LevelTwoOldXStarEndpoint.local_potential
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T19:57:43.324676+00:00
-- url     : https://prove2.me/submissions/8e7d2d4c-c648-486c-a344-ca31243bccf4

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDecoder
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalXStarTransport
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoOldXStarEndpoint
import Theorems.Thm_QEC_Coding_BDL26LevelTwoDistance_rxCoboundary1_localFace
import Theorems.Thm_QEC_Coding_BDL26LevelTwoDistance_xCylinder_coboundary_eq_cocycle
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26LevelTwoOldXStarEndpoint
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26RZLocalReplacement BDL26RZMap1CoordinateBridge
open BDL26ReplacementCochainMaps BDL26LevelTwoCode BDL26LevelTwoDistance
open BDL26LevelTwoDecoder BDL26DecodingGraph
open scoped Classical BigOperators
namespace QEC.Coding.BDL26LevelTwoOldXStarEndpoint
theorem _root_.solution (S : OddScale) (x : BaseX) (w : W1 S)
    (hc : rxCoboundary1 Seed S w=0) :
    ∃ f : Word F (DoubleCylinderVertex Seed x S),
      wordLinearMapTranspose (rxCx Seed x S).boundary1 f=
        fun e => w (Sum.inl ⟨x,e⟩) := by
  have hc' : wordLinearMapTranspose (rxCx Seed x S).boundary2
      (fun e => w (Sum.inl ⟨x,e⟩))=0 := by
    funext face
    exact (rxCoboundary1_localFace Seed S w x face).symm.trans
      (congrFun hc (Sum.inl (Sum.inl ⟨x,face⟩)))
  have hm := ((rxCx Seed x S).mem_middleCocycleCode_iff _).mpr hc'
  rw [← xCylinder_coboundary_eq_cocycle Seed baseTannerSquareAdmissibleV4.toTannerSquareAdmissibleV3
    baseTannerSquareCellularRegular x S] at hm
  exact ((rxCx Seed x S).mem_firstCoboundaryCheckCode_iff _).mp hm
end QEC.Coding.BDL26LevelTwoOldXStarEndpoint
