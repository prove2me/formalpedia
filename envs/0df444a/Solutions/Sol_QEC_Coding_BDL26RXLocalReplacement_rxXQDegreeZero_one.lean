-- Prove2me | solution 1 for QEC.Coding.BDL26RXLocalReplacement.rxXQDegreeZero_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T01:16:15.055731+00:00
-- url     : https://prove2.me/submissions/27bceab0-b4c2-4854-9c51-f542d130156b

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
theorem _root_.solution (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (q : P.Q) (x : P.X)
    (hxq : P.xq x q = true) (S : OddScale) :
    rxXQDegreeZero P A q x hxq S (1 : Word Field (DoubleCylinderVertex P x S)) =
      (1 : Word Field (QDoubleCylinderVertex P q S)) := by
  rfl
end QEC.Coding.BDL26RXLocalReplacement
