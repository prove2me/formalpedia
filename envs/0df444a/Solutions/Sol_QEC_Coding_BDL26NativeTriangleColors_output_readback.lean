-- Prove2me | solution 1 for QEC.Coding.BDL26NativeTriangleColors.output_readback
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T02:12:51.933188+00:00
-- url     : https://prove2.me/submissions/8d40005b-36aa-405e-b19e-be183b1b1d35

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeSupportMetadata
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleKeys
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleColors
import Theorems.Thm_QEC_Coding_BDL26NativeTriangleColors_colors_value
import Theorems.Thm_QEC_Coding_BDL26NativeTriangleColors_row_actual
import Theorems.Thm_QEC_Coding_BDL26NativeTriangleKeys_triangle_readback


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26NativeTriangleColors
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26RandomPerturbation BDL26BoundedValence
open G
noncomputable section
open scoped Classical
namespace QEC.Coding.BDL26NativeTriangleColors
theorem _root_.solution (S : OddScale) (n : ℕ) (t : Triangle (P S n)) :
    (colorsQ S n).value[(BDL26NativeTriangleKeys.nativeTriangleIndex S n t).val]?=
      some (nativeRow S n t) := by
  rw [colors_value,List.getElem?_map,BDL26NativeTriangleKeys.triangle_readback,
    Option.map_some,row_actual]
end QEC.Coding.BDL26NativeTriangleColors
