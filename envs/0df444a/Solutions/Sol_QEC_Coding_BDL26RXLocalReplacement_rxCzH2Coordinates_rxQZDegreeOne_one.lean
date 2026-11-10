-- Prove2me | solution 1 for QEC.Coding.BDL26RXLocalReplacement.rxCzH2Coordinates_rxQZDegreeOne_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T01:16:59.834742+00:00
-- url     : https://prove2.me/submissions/8229cb49-7295-4fdf-83fd-f96b3ff51c76

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalRegularity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BoundedValence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXLocalReplacement

set_option autoImplicit false
open QEC
open QEC.Coding
open QEC.Coding.BDL26RXLocalReplacement
open BDL26FiniteAlternatingCore
open BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity
universe u
namespace QEC.Coding.BDL26RXLocalReplacement
theorem _root_.solution
    (P : TannerSquarePresentation) (q : P.Q) (z : P.Z)
    (hqz : P.qz q z = true) (S : OddScale) :
    rxCzH2Coordinates P z
        ((LinearMap.range
          (wordLinearMapTranspose (rxCz P z).boundary2)).mkQ
      (rxQZDegreeOne P q z hqz S
            (1 : Word Field (QDoubleCylinderVertex P q S)))) = (1, 1) := by
  rfl
end QEC.Coding.BDL26RXLocalReplacement
