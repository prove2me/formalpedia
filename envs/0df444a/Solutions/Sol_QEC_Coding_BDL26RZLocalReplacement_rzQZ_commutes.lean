-- Prove2me | solution 1 for QEC.Coding.BDL26RZLocalReplacement.rzQZ_commutes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T14:45:54.227209+00:00
-- url     : https://prove2.me/submissions/28d7e200-ddcf-4667-b74f-50183932598d

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalRegularity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZLocalReplacement

set_option autoImplicit false
open QEC
open QEC.Coding
open QEC.Coding.BDL26RZLocalReplacement
open BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity
namespace QEC.Coding.BDL26RZLocalReplacement
theorem _root_.solution (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (q : P.Q) (z : P.Z)
    (hqz : P.qz q z = true) (S : OddScale) :
    (rzQZDegreeOne P A q z hqz S).comp
        (qDoubleCylinderBoundary1 (transposePresentation P) q S) =
      (doubleCylinderBoundary1 (transposePresentation P) z S).comp
        (rzQZDegreeZero P A q z hqz S) := by
  rw [← rzCzGraphBoundary_eq_boundary1]
  exact rzQZ_graph_commutes P A q z hqz S
end QEC.Coding.BDL26RZLocalReplacement
