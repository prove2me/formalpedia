-- Prove2me | solution 1 for QEC.Coding.BDL26RXLocalReplacement.rxCzH0Coordinate_bijective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T01:13:44.390438+00:00
-- url     : https://prove2.me/submissions/b1a6012f-294a-4d2f-afa3-bb13e0bf2f63

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
theorem _root_.solution (P : TannerSquarePresentation) (z : P.Z) :
    Function.Bijective (rxCzH0Coordinate P z) := by
  constructor
  · intro first second _
    exact Subsingleton.elim first second
  · intro value
    exact ⟨0, Subsingleton.elim _ value⟩
end QEC.Coding.BDL26RXLocalReplacement
