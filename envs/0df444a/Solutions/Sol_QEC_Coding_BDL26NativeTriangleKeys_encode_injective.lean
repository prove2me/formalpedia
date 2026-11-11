-- Prove2me | solution 1 for QEC.Coding.BDL26NativeTriangleKeys.encode_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T00:56:50.87791+00:00
-- url     : https://prove2.me/submissions/40a89056-28ef-4c11-a9fd-63365191a7f4

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_NativePresentationGenerator
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleKeys
import Theorems.Thm_QEC_Coding_BDL26NativePresentationGenerator_triangles_injective


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26NativeTriangleKeys
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RandomPerturbation
open BDL26DecodingGraph
noncomputable section
namespace QEC.Coding.BDL26NativeTriangleKeys
theorem _root_.solution (S : OddScale) (n : ℕ) : Function.Injective (encode S n) :=
  BDL26NativePresentationGenerator.triangles_injective S n
end QEC.Coding.BDL26NativeTriangleKeys
