-- Prove2me | solution 1 for QEC.Coding.BDL26RXPhysicalCoordinateTrace.primitive_positive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T08:07:17.352029+00:00
-- url     : https://prove2.me/submissions/107f7549-5aba-4c62-bd62-cc2c071b6209

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
theorem _root_.solution {S : OddScale} {b : Nat} (p : Primitive S b) : 1≤b := by
  rcases primitiveDataEquiv S b p with ⟨h,q,e,d⟩ | ⟨ho,x,c,d⟩
  · omega
  · omega
end QEC.Coding.BDL26RXPhysicalCoordinateTrace
