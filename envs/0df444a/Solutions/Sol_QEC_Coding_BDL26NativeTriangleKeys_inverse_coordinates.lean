-- Prove2me | solution 1 for QEC.Coding.BDL26NativeTriangleKeys.inverse_coordinates
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T02:04:02.676429+00:00
-- url     : https://prove2.me/submissions/12bd4372-9554-49b4-b724-09339162c2c9

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_NativePresentationGenerator
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleKeys
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26NativeTriangleKeys
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RandomPerturbation
open BDL26DecodingGraph
noncomputable section
namespace QEC.Coding.BDL26NativeTriangleKeys
theorem _root_.solution (S : OddScale) (n : ℕ) (k : Fin (triangleCount S n)) :
    ((BDL26NativePresentationGenerator.generatedRefines S n).fIndex ((nativeTriangleIndex S n).symm k).1).val=
        k.val/2 ∧ ((nativeTriangleIndex S n).symm k).2.val=k.val%2 := by
  exact ⟨congrArg Fin.val ((BDL26NativePresentationGenerator.generatedRefines S n).fIndex.apply_symm_apply _),rfl⟩
end QEC.Coding.BDL26NativeTriangleKeys
