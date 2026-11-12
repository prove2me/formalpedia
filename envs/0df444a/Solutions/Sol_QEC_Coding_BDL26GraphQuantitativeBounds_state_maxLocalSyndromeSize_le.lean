-- Prove2me | solution 1 for QEC.Coding.BDL26GraphQuantitativeBounds.state_maxLocalSyndromeSize_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T22:12:13.508427+00:00
-- url     : https://prove2.me/submissions/f643e21c-0cea-4124-ae66-1506fa039938

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BoundedValenceSuccessors
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementSupport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Theorems.Thm_QEC_Coding_BDL26GraphQuantitativeBounds_maxLocalSyndromeSize_le
import Theorems.Thm_QEC_Coding_BDL26BoundedValence_state_boundedValence


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26GraphQuantitativeBounds
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26QuantitativeBounds BDL26BoundedValence
open BDL26FiniteAlternatingCore BDL26RXLocalReplacement
open scoped BigOperators Classical
open BDL26ReplacementSupport
namespace QEC.Coding.BDL26GraphQuantitativeBounds
theorem _root_.solution (S : OddScale) (n : Nat) :
    maxLocalSyndromeSize (state S n).presentation S ≤ localCoordinateBound S :=
  maxLocalSyndromeSize_le _ (state S n).admissible.toTannerSquareAdmissible
    (state_boundedValence S n) S
end QEC.Coding.BDL26GraphQuantitativeBounds
