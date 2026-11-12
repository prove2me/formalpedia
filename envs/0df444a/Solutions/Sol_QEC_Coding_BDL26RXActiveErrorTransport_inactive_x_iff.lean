-- Prove2me | solution 1 for QEC.Coding.BDL26RXActiveErrorTransport.inactive_x_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T10:41:47.856456+00:00
-- url     : https://prove2.me/submissions/6b1a4771-6c8a-4ce1-97d4-8ef77572112e

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXFiniteBlockTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXActiveErrorTransport
import Theorems.Thm_QEC_Coding_BDL26RXActiveErrorTransport_mem_activeX_iff

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXActiveErrorTransport
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RXDecoderAdapter BDL26RXErrorPullback
open BDL26RZMap1CoordinateBridge BDL26RXXStarTransport MultiscaleDecoder RXCoarseGraining
open RXCoarseGraining.RXCoarseGrainingData
open BDL26BoundedValence BDL26GraphQuantitativeBounds
open scoped BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (h : i.val % 2=0)
namespace QEC.Coding.BDL26RXActiveErrorTransport
theorem _root_.solution (E : Upper S depth i) (x : XCoord S i) :
    x ∉ activeX S depth i h E ↔
      restrictWordLinear ((rxLx S depth i h).correctionRegion x) E=0 := by
  constructor
  · intro hx
    funext p
    by_contra hn
    exact hx ((mem_activeX_iff S depth i h E x).mpr ⟨p.val,p.property,hn⟩)
  · intro hz hx
    obtain ⟨p,hp,hn⟩ := (mem_activeX_iff S depth i h E x).mp hx
    exact hn (congrFun hz ⟨p,hp⟩)
end QEC.Coding.BDL26RXActiveErrorTransport
