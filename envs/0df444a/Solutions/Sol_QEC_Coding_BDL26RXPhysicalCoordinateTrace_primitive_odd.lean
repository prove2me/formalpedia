-- Prove2me | solution 1 for QEC.Coding.BDL26RXPhysicalCoordinateTrace.primitive_odd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T08:12:41.778621+00:00
-- url     : https://prove2.me/submissions/8c829428-5de4-4bf7-878a-0bbca9de0088

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXQEdgePairTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXFaceEdgeTower
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXPhysicalCoordinateTrace

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXPhysicalCoordinateTrace
open MultiscaleDecoder BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26CSSHamiltonian BDL26ActualFailureReadout
open BDL26RZMap1CoordinateBridge BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26HistorySyndromeSensitivity BDL26TannerLocalRegularity
open scoped Classical
namespace QEC.Coding.BDL26RXPhysicalCoordinateTrace
theorem _root_.solution {S : OddScale} {b : Nat} (p : Primitive S b) : ¬b%2=0 := by
  rcases primitiveDataEquiv S b p with ⟨h,q,e,d⟩ | ⟨ho,x,c,d⟩
  · subst b
    decide
  · exact ho
end QEC.Coding.BDL26RXPhysicalCoordinateTrace
