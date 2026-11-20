-- Prove2me | solution 1 for QEC.Coding.BDL26RXPrimitiveFailureLocalization.safe_correction_equation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:35:45.623774+00:00
-- url     : https://prove2.me/submissions/d19ac257-08f9-4d4e-8620-ab1974f777c0

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXPhysicalCoordinateTrace_Semantics
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXPrimitiveFailureLocalization
import Theorems.Thm_QEC_Coding_BDL26FirstZeroEmptySuffix_original_correction_equation
import Theorems.Thm_QEC_Coding_BDL26FirstZeroFaceEndpoint_original_correction_equation
import Theorems.Thm_QEC_Coding_BDL26FirstZeroQVertexTower_original_correction_equation
import Theorems.Thm_QEC_Coding_BDL26LocalSearchFailureReduction_original_correction_equation
import Theorems.Thm_QEC_Coding_BDL26RXFaceEdgeTower_original_correction_equation


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXPrimitiveFailureLocalization
open MultiscaleDecoder PauliSymplectic BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26CSSHamiltonian BDL26ActualFailureReadout
open BDL26HistorySyndromeSensitivity BDL26HistoryErrorTelescoping BDL26HistoryLogicalResidual
open BDL26LocalizedHistoryErrorDescent BDL26RZMap1CoordinateBridge
open BDL26RXLocalReplacement BDL26RZLocalReplacement BDL26OwnerIncidenceMasks
open BDL26LevelTwoCode BDL26LevelTwoDistance BDL26TannerLocalRegularity
open BDL26TransposedStoppedDecoder BDL26RXPhysicalCoordinateTrace
open scoped Classical BigOperators
namespace QEC.Coding.BDL26RXPrimitiveFailureLocalization
theorem _root_.solution (S : OddScale) (N : Nat) (u : XSyndromeDomain S N)
    (q : Physical S (N+2)) (hs : firstReadout S N u=0)
    (hSafe : (parse S N q).safe=true) :
    (SuffixData S N).family.coboundary0 (TopIndex N) (safeFullPotential S N u q hs hSafe)=
      flip S N q+xCorrection S N u+xCorrection S N (translateX S N u (flip S N q)) :=
  BDL26LocalSearchFailureReduction.original_correction_equation S N u q hs
    (safe_search S N u q hs hSafe)
end QEC.Coding.BDL26RXPrimitiveFailureLocalization
