-- Prove2me | solution 1 for QEC.Coding.BDL26RXXStarTransport.gradientError_nonzero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T23:19:53.812583+00:00
-- url     : https://prove2.me/submissions/e15a1279-d619-4583-adbe-766d9f69e519

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXQBlockTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXXStarTransport_Geometry
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_boundaryGradient_nonzero
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_gradientError_restriction
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


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
theorem _root_.solution (x : XCoord S i) : gradientError S depth i h x ≠ 0 := by
  intro hz
  have he := gradientError_restriction S depth i h x
  rw [hz,map_zero] at he
  exact boundaryGradient_nonzero S depth i h x he.symm
end QEC.Coding.BDL26RXXStarTransport
