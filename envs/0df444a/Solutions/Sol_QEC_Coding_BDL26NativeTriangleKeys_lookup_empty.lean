-- Prove2me | solution 1 for QEC.Coding.BDL26NativeTriangleKeys.lookup_empty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T02:00:39.156287+00:00
-- url     : https://prove2.me/submissions/40c9bc7d-f22b-422d-a169-1402373b21a6

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_NativePresentationGenerator
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleKeys

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26NativeTriangleKeys
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RandomPerturbation
open BDL26DecodingGraph
namespace QEC.Coding.BDL26NativeTriangleKeys
theorem _root_.solution (c : Code) : lookupRowsQ c []=(none,1,0) := rfl
end QEC.Coding.BDL26NativeTriangleKeys
