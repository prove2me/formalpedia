-- Prove2me | solution 1 for QEC.Coding.BDL26RXActiveErrorTransport.inactive_q_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T10:42:03.736575+00:00
-- url     : https://prove2.me/submissions/8033ceb6-ec3e-4620-a38b-6cd34e7b392d

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXFiniteBlockTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXActiveErrorTransport
import Theorems.Thm_QEC_Coding_BDL26RXActiveErrorTransport_mem_activeQ_iff

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
theorem _root_.solution (E : Upper S depth i) (q : QCoord S i) :
    q ∉ activeQ S depth i h E ↔
      restrictWordLinear ((rxLq S depth i h).correctionRegion q) E=0 := by
  constructor
  · intro hq
    funext p
    by_contra hn
    exact hq ((mem_activeQ_iff S depth i h E q).mpr ⟨p.val,p.property,hn⟩)
  · intro hz hq
    obtain ⟨p,hp,hn⟩ := (mem_activeQ_iff S depth i h E q).mp hq
    exact hn (congrFun hz ⟨p,hp⟩)
end QEC.Coding.BDL26RXActiveErrorTransport
