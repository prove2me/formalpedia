-- Prove2me | solution 1 for QEC.Coding.BDL26GraphQuantitativeBounds.rzParentFiber_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T05:47:07.197205+00:00
-- url     : https://prove2.me/submissions/d7a5ac4e-ef35-4393-966a-5d5440c3d932

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BoundedValenceSuccessors
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementSupport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Theorems.Thm_QEC_Coding_BDL26GraphQuantitativeBounds_rzParentFiber_card_le
import Theorems.Thm_QEC_Coding_BDL26GraphQuantitativeBounds_rzZeroCell_card_le
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26GraphQuantitativeBounds
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26QuantitativeBounds BDL26BoundedValence
open BDL26FiniteAlternatingCore BDL26RXLocalReplacement
open scoped BigOperators Classical
namespace QEC.Coding.BDL26GraphQuantitativeBounds
theorem _root_.solution (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (h : BoundedValence P) (S : OddScale) (u : Vertex P) :
    Fintype.card {v : Vertex (BDL26RZLocalReplacement.rzReplacementPresentation P A S) //
      rzParent P A S v = some u} ≤ localCoordinateBound S :=
  (rzParentFiber_card_le P A S u).trans (rzZeroCell_card_le P A h S u)
end QEC.Coding.BDL26GraphQuantitativeBounds
