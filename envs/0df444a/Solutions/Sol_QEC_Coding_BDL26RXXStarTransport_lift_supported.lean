-- Prove2me | solution 1 for QEC.Coding.BDL26RXXStarTransport.lift_supported
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T12:46:08.351146+00:00
-- url     : https://prove2.me/submissions/b183625f-3a0c-44ca-844e-c04389e4dce7

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXQBlockTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXXStarTransport_Geometry
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_support_of_zero_off
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_rxXLift_other


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXXStarTransport
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RXDecoderAdapter BDL26RXErrorPullback
open BDL26RZMap1CoordinateBridge MultiscaleDecoder RXCoarseGraining
open RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (h : i.val % 2=0)
namespace QEC.Coding.BDL26RXXStarTransport
theorem _root_.solution (x : XCoord S i) (s : LocalPotential S i x) :
    hammingSupport ((rxContract S depth i h).support_decomposition.cxLift0 x s) ⊆
      degreeZeroBlock S depth i h x := by
  apply support_of_zero_off
  intro p hp
  obtain ⟨⟨y,v⟩,rfl⟩ := (rxDegreeZeroEquiv S depth i h).surjective p
  have hy : y≠x := by
    intro he
    subst y
    exact hp (Finset.mem_image.mpr ⟨v,Finset.mem_univ _,rfl⟩)
  exact rxXLift_other S depth i h x y hy s v
end QEC.Coding.BDL26RXXStarTransport
