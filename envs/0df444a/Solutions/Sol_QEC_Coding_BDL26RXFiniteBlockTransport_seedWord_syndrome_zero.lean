-- Prove2me | solution 1 for QEC.Coding.BDL26RXFiniteBlockTransport.seedWord_syndrome_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T14:02:37.197646+00:00
-- url     : https://prove2.me/submissions/aa77ea9d-8a99-41b8-b014-ceafd8697bc0

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXXStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXFiniteBlockTransport
import Theorems.Thm_QEC_Coding_BDL26RZMap1CoordinateBridge_tannerCoboundary1_canonicalBasis_apply
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans
attribute [local simp] QEC.Coding.BDL26RZMap1CoordinateBridge.tannerCoboundary1_canonicalBasis_apply



set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXFiniteBlockTransport
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RXDecoderAdapter BDL26RXErrorPullback
open BDL26RZMap1CoordinateBridge BDL26RXXStarTransport MultiscaleDecoder RXCoarseGraining
open RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (h : i.val % 2=0)
open BDL26FiniteAlternatingCore
namespace QEC.Coding.BDL26RXFiniteBlockTransport
theorem _root_.solution : tannerCoboundary1 baseTannerSquarePresentation seedWord (0 : BaseZ)=0 := by
  let q0 : baseTannerSquarePresentation.Q := (0 : BaseQubit)
  let q4 : baseTannerSquarePresentation.Q := (4 : BaseQubit)
  let z0 : baseTannerSquarePresentation.Z := (0 : BaseZ)
  change tannerCoboundary1 baseTannerSquarePresentation
    (canonicalBasisWord (F := BDL26RZMap1CoordinateBridge.Field) q0+
      canonicalBasisWord (F := BDL26RZMap1CoordinateBridge.Field) q4)
    z0=(0 : BDL26RZMap1CoordinateBridge.Field)
  have hm := congrFun ((tannerCoboundary1 baseTannerSquarePresentation).map_add
    (canonicalBasisWord (F := BDL26RZMap1CoordinateBridge.Field) q0)
    (canonicalBasisWord (F := BDL26RZMap1CoordinateBridge.Field) q4)) z0
  have h0 := tannerCoboundary1_canonicalBasis_apply baseTannerSquarePresentation q0 z0
  have h4 := tannerCoboundary1_canonicalBasis_apply baseTannerSquarePresentation q4 z0
  exact hm.trans ((congrArg₂ (fun a b : BDL26RZMap1CoordinateBridge.Field => a+b) h0 h4).trans
    (by decide))
end QEC.Coding.BDL26RXFiniteBlockTransport
