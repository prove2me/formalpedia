-- Prove2me | solution 1 for QEC.Coding.BDL26RXPrimitiveFailureLocalization.safe_base_identity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T09:40:14.378582+00:00
-- url     : https://prove2.me/submissions/06c7fae6-3079-4423-aa1f-d75a084acf86

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXPhysicalCoordinateTrace_Semantics
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXPrimitiveFailureLocalization
import Theorems.Thm_QEC_Coding_BDL26ActualFailureReadout_basePotential_spec
import Theorems.Thm_QEC_Coding_BDL26LocalSearchFailureReduction_basePotential_spec


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
    (SuffixData S N).family.coboundary0 0
      (BDL26LocalSearchFailureReduction.basePotential S N u q hs (safe_search S N u q hs hSafe))=
      (descent S N u q).word+
        (actualBase S N).decode (actualInputs S N (input S N u) 0)+
        (actualBase S N).decode
          (actualInputs S N (perturbTop S N (input S N u) (flip S N q)) 0) :=
  BDL26LocalSearchFailureReduction.basePotential_spec S N u q hs (safe_search S N u q hs hSafe)
end QEC.Coding.BDL26RXPrimitiveFailureLocalization
