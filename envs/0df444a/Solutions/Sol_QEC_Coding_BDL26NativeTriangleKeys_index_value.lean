-- Prove2me | solution 1 for QEC.Coding.BDL26NativeTriangleKeys.index_value
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T01:29:52.566618+00:00
-- url     : https://prove2.me/submissions/75e07402-cb4d-4702-9d65-71ff4099b1bf

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_NativePresentationGenerator
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleKeys

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26NativeTriangleKeys
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RandomPerturbation
open BDL26DecodingGraph
noncomputable section
namespace QEC.Coding.BDL26NativeTriangleKeys
theorem _root_.solution (S : OddScale) (n : ℕ) (t : Triangle (P S n)) :
    (nativeTriangleIndex S n t).val=
      2*((BDL26NativePresentationGenerator.generatedRefines S n).fIndex t.1).val+t.2.val := rfl
end QEC.Coding.BDL26NativeTriangleKeys
