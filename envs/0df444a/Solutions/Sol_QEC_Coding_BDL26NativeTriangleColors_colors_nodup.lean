-- Prove2me | solution 1 for QEC.Coding.BDL26NativeTriangleColors.colors_nodup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T02:10:19.35243+00:00
-- url     : https://prove2.me/submissions/3a5caa05-44cf-4871-941a-ceaaeb99f538

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeSupportMetadata
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleKeys
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleColors
import Theorems.Thm_QEC_Coding_BDL26NativeTriangleColors_colors_order
import Theorems.Thm_QEC_Coding_BDL26NativePresentationGenerator_output_label_nodup


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26NativeTriangleColors
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26RandomPerturbation BDL26BoundedValence
open G
namespace QEC.Coding.BDL26NativeTriangleColors
theorem _root_.solution (S : OddScale) (n : ℕ) : (colorsQ S n).value.Nodup := by
  apply List.Nodup.of_map Prod.fst
  rw [colors_order]
  exact (BDL26NativePresentationGenerator.output_label_nodup S n).2.2
end QEC.Coding.BDL26NativeTriangleColors
