-- Prove2me | solution 1 for QEC.Coding.BDL26TopOwnerIsolation.markedAdjacent_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T00:12:26.464755+00:00
-- url     : https://prove2.me/submissions/d3ebacb9-2807-4319-ba72-8695d66cbe8f

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_DecodingGraph
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TopOwnerIsolation

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26TopOwnerIsolation
open BDL26FiniteTannerSquare BDL26DecodingGraph MultiscaleDecoder
open scoped Classical
namespace QEC.Coding.BDL26TopOwnerIsolation
theorem _root_.solution (M : Finset Node)
    (u v : {w : Node // w ∈ M}) :
    markedAdjacent M u v ↔ graph.adjacent u.val v.val := Iff.rfl
end QEC.Coding.BDL26TopOwnerIsolation
