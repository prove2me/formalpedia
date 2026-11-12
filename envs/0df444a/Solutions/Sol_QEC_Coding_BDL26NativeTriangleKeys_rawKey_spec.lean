-- Prove2me | solution 1 for QEC.Coding.BDL26NativeTriangleKeys.rawKey_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T01:59:40.57699+00:00
-- url     : https://prove2.me/submissions/b2eb3b76-63e5-4a56-9676-50e1923c07a6

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_NativePresentationGenerator
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleKeys

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26NativeTriangleKeys
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RandomPerturbation
open BDL26DecodingGraph
namespace QEC.Coding.BDL26NativeTriangleKeys
theorem _root_.solution (c : Code) :
    (rawKeyQ c).1=2*c.owner+c.copy ∧ operations (rawKeyQ c)=5 ∧
      allocations (rawKeyQ c)=0 := ⟨rfl,rfl,rfl⟩
end QEC.Coding.BDL26NativeTriangleKeys
