-- Prove2me | solution 1 for QEC.Coding.BDL26RZLocalReplacement.rzXQDegreeZero_totalParity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T14:03:59.095354+00:00
-- url     : https://prove2.me/submissions/a0548684-9db6-4952-be01-cea51be830c7

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
    (q : P.Q) (x : P.X) (hxq : P.xq x q = true) (S : OddScale)
    (word : Word Field Two) :
    totalParity (rzXQDegreeZero P q x hxq S word) =
      word 0 + word 1 := by
  rw [rzXQDegreeZero, totalParity_wordPushforward]
  change (∑ copy : Two, word copy) = _
  exact Fin.sum_univ_two word
end QEC.Coding.BDL26RZLocalReplacement
