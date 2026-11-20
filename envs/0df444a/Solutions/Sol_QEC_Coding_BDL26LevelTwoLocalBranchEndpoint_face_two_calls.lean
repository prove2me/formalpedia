-- Prove2me | solution 1 for QEC.Coding.BDL26LevelTwoLocalBranchEndpoint.face_two_calls
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:06:46.651906+00:00
-- url     : https://prove2.me/submissions/cc101809-8b7a-4799-9d57-b50c38896481

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDecoderZero
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalXStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoLocalBranchEndpoint
import Theorems.Thm_QEC_Coding_BDL26LevelTwoLocalBranchEndpoint_face_parity_zero
import Theorems.Thm_QEC_Coding_BDL26LevelTwoLocalBranchEndpoint_zero_parity_two_calls

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26LevelTwoLocalBranchEndpoint
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26RXLocalReplacement BDL26RZLocalReplacement BDL26LevelTwoCode
open BDL26LevelTwoDistance BDL26RZMap1CoordinateBridge BDL26ReplacementCochainMaps
open scoped BigOperators
open scoped Classical
namespace QEC.Coding.BDL26LevelTwoLocalBranchEndpoint
theorem _root_.solution (S : OddScale) (z : (P S).Z)
    (f : ZDoubleCylinderFace (P S) z S) (h : Error S) (s t : Syndrome S)
    (hh : supported S (.inl (.inl ⟨z,f⟩)) h) (hd : delta S h=s+t)
    (hs : localSuccess S s) (ht : localSuccess S t) :
    ∃ p : Potential S, boundary S p=h+D S s+D S t :=
  zero_parity_two_calls S h s t hd (face_parity_zero S z f h hh) hs ht
end QEC.Coding.BDL26LevelTwoLocalBranchEndpoint
