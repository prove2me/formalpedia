-- Prove2me | solution 1 for QEC.Coding.BDL26NativeTriangleKeys.encode_member
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T23:51:50.382361+00:00
-- url     : https://prove2.me/submissions/17d02797-7afe-4eed-b08f-345bffd28f74

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_NativePresentationGenerator
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleKeys
import Theorems.Thm_QEC_Coding_BDL26NativePresentationGenerator_triangle_labels


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26NativeTriangleKeys
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RandomPerturbation
open BDL26DecodingGraph
noncomputable section
namespace QEC.Coding.BDL26NativeTriangleKeys
theorem _root_.solution (S : OddScale) (n : ℕ) (t : Triangle (P S n)) :
    encode S n t∈(BDL26NativePresentationGenerator.setupQ S n).1.triangles :=
  (BDL26NativePresentationGenerator.triangle_labels S n _).mpr ⟨t,rfl⟩
end QEC.Coding.BDL26NativeTriangleKeys
