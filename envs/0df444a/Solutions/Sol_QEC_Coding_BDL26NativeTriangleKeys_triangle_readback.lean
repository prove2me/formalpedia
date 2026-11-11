-- Prove2me | solution 1 for QEC.Coding.BDL26NativeTriangleKeys.triangle_readback
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T01:44:34.891079+00:00
-- url     : https://prove2.me/submissions/6143a12a-3f3d-4939-80f2-a120d976181c

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_NativePresentationGenerator
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleKeys
import Theorems.Thm_QEC_Coding_BDL26NativeTriangleKeys_encode_readback

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26NativeTriangleKeys
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RandomPerturbation
open BDL26DecodingGraph
noncomputable section
namespace QEC.Coding.BDL26NativeTriangleKeys
theorem _root_.solution (S : OddScale) (n : ℕ) (t : Triangle (P S n)) :
    (BDL26NativePresentationGenerator.setupQ S n).1.triangles[(nativeTriangleIndex S n t).val]?=
      some (encode S n t) := by
  have hk : (nativeTriangleIndex S n t).val<
      2*(BDL26NativePresentationGenerator.setupQ S n).1.data.frame.nf := by
    calc
      (nativeTriangleIndex S n t).val<triangleCount S n := (nativeTriangleIndex S n t).isLt
      _=2*(BDL26NativePresentationGenerator.setupQ S n).1.data.frame.nf := triangle_count S n
  change (BDL26NativePresentationGenerator.triangleCodesQ _).1[_]?=_
  rw [triangle_codes,frame_codes_dense]
  have hr : (nativeTriangleIndex S n t).val<
      2*(BDL26NativePresentationGenerator.runQ S n).1.frame.nf := hk
  rw [List.getElem?_map,List.getElem?_range hr,Option.map_some]
  exact congrArg some (encode_readback S n t)
end QEC.Coding.BDL26NativeTriangleKeys
