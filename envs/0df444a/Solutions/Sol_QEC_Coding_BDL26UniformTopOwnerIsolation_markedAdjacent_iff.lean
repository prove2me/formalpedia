-- Prove2me | solution 1 for QEC.Coding.BDL26UniformTopOwnerIsolation.markedAdjacent_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T00:20:15.74484+00:00
-- url     : https://prove2.me/submissions/098a4ca3-0be8-4e7c-8ada-19684216c462

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TopOwnerIsolation
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformIsolation

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26UniformTopOwnerIsolation
open BDL26FiniteTannerSquare BDL26DecodingGraph MultiscaleDecoder
open scoped Classical
namespace QEC.Coding.BDL26UniformTopOwnerIsolation
theorem _root_.solution (S : OddScale) (n : Nat) (M : Finset (Node S n))
    (u v : {w : Node S n // w ∈ M}) :
    markedAdjacent S n M u v ↔ (graph S n).adjacent u.val v.val := Iff.rfl
end QEC.Coding.BDL26UniformTopOwnerIsolation
