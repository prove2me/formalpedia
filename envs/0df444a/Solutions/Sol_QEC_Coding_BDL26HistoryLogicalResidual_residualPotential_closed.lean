-- Prove2me | solution 1 for QEC.Coding.BDL26HistoryLogicalResidual.residualPotential_closed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T00:36:23.635934+00:00
-- url     : https://prove2.me/submissions/54c9ccce-f040-4d3d-8f92-fb2671463b13

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryLogicalResidual_Intervals
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryLogicalResidual_Words
import Theorems.Thm_QEC_Coding_MultiscaleDecoder_BDL26CochainFamily_coboundary1_comp_coboundary0


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26HistoryLogicalResidual
open MultiscaleDecoder BDL26HistorySyndromeSensitivity BDL26HistoryErrorTelescoping
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder BDL26OwnerIncidenceMasks
open BDL26RZMap1CoordinateBridge
open scoped Classical
variable (S : OddScale) (n : Nat)
namespace QEC.Coding.BDL26HistoryLogicalResidual
theorem _root_.solution (e u : (SuffixData S n).family.Cochain1 (TopIndex n)) :
    (SuffixData S n).family.coboundary1 (TopIndex n)
      ((SuffixData S n).family.coboundary0 (TopIndex n) (residualPotential S n e u)) = 0 :=
  LinearMap.congr_fun ((SuffixData S n).family.coboundary1_comp_coboundary0 (TopIndex n)) _
end QEC.Coding.BDL26HistoryLogicalResidual
