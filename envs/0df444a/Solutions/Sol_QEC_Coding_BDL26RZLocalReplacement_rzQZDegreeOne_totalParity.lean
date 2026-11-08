-- Prove2me | solution 1 for QEC.Coding.BDL26RZLocalReplacement.rzQZDegreeOne_totalParity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T14:04:01.010257+00:00
-- url     : https://prove2.me/submissions/51e9e4ae-986e-4e62-9bc9-c6519e751b60

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalRegularity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZLocalReplacement
import Theorems.Thm_QEC_Coding_BDL26RZLocalReplacement_totalParity_wordPushforward

set_option autoImplicit false
open QEC
open QEC.Coding
open QEC.Coding.BDL26RZLocalReplacement
open BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity
namespace QEC.Coding.BDL26RZLocalReplacement
theorem _root_.solution (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (q : P.Q) (z : P.Z)
    (hqz : P.qz q z = true) (S : OddScale)
    (word : Word Field (QDoubleCylinderVertex (transposePresentation P) q S)) :
    totalParity (rzQZDegreeOne P A q z hqz S word) = totalParity word := by
  classical
  exact totalParity_wordPushforward _ word
end QEC.Coding.BDL26RZLocalReplacement
