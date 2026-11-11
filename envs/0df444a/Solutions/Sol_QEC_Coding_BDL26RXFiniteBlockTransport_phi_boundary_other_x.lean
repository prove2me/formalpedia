-- Prove2me | solution 1 for QEC.Coding.BDL26RXFiniteBlockTransport.phi_boundary_other_x
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T13:58:35.994085+00:00
-- url     : https://prove2.me/submissions/205302f6-ab47-4e11-a3e7-81ff49c5c7eb

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXXStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXFiniteBlockTransport
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_potential_boundary_other_x
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXFiniteBlockTransport
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RXDecoderAdapter BDL26RXErrorPullback
open BDL26RZMap1CoordinateBridge BDL26RXXStarTransport MultiscaleDecoder RXCoarseGraining
open RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (h : i.val % 2=0)
namespace QEC.Coding.BDL26RXFiniteBlockTransport
theorem _root_.solution (X0 : Finset (XCoord S i)) (x : XCoord S i) (hx : x ∉ X0)
    (a b : Upper S depth i) :
    restrictWordLinear ((rxLx S depth i h).correctionRegion x)
      ((indexedFamily S depth).coboundary0 i.succ (Phi S depth i h X0 a b))=0 := by
  rw [Phi,map_sum,map_sum]
  apply Finset.sum_eq_zero
  intro y hy
  exact potential_boundary_other_x S depth i h y x (fun hh => hx (hh.symm ▸ hy)) a b
end QEC.Coding.BDL26RXFiniteBlockTransport
