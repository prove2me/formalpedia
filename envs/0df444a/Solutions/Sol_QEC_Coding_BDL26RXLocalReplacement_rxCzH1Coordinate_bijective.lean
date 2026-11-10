-- Prove2me | solution 1 for QEC.Coding.BDL26RXLocalReplacement.rxCzH1Coordinate_bijective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T01:13:50.342452+00:00
-- url     : https://prove2.me/submissions/12157d6a-a25b-46d5-82ea-cb3b75a4bd4d

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
    Function.Bijective (rxCzH1Coordinate P z) := by
  constructor
  · intro first second _
    exact Subsingleton.elim first second
  · intro value
    exact ⟨0, Subsingleton.elim _ value⟩
end QEC.Coding.BDL26RXLocalReplacement
