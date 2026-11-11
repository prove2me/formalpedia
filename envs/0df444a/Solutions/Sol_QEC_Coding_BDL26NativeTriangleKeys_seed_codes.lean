-- Prove2me | solution 1 for QEC.Coding.BDL26NativeTriangleKeys.seed_codes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T01:28:40.444002+00:00
-- url     : https://prove2.me/submissions/0f2385ab-3609-46dd-8433-e40ee216a114

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_NativePresentationGenerator
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleKeys

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26NativeTriangleKeys
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RandomPerturbation
open BDL26DecodingGraph
namespace QEC.Coding.BDL26NativeTriangleKeys
theorem _root_.solution (S : OddScale) :
    (BDL26NativePresentationGenerator.setupQ S 0).1.triangles=frameCodes 4 := by
  change (BDL26NativePresentationGenerator.triangleCodesQ _).1=_
  rw [triangle_codes]
  rfl
end QEC.Coding.BDL26NativeTriangleKeys
