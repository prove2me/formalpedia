-- Prove2me | solution 1 for QEC.Coding.BDL26RXLocalReplacement.rxCqH0Coordinate_bijective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T01:13:27.960696+00:00
-- url     : https://prove2.me/submissions/3f022989-6ab6-4504-81e8-897c1fe21414

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
    (q : P.Q) (S : OddScale) :
    Function.Bijective (rxCqH0Coordinate P q S) := by
  constructor
  · intro first second _
    exact Subsingleton.elim first second
  · intro value
    exact ⟨0, Subsingleton.elim _ value⟩
end QEC.Coding.BDL26RXLocalReplacement
