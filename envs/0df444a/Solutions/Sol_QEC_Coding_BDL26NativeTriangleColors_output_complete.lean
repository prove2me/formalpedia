-- Prove2me | solution 1 for QEC.Coding.BDL26NativeTriangleColors.output_complete
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T02:13:57.424469+00:00
-- url     : https://prove2.me/submissions/978a94bf-6fa1-469f-bec7-9cc1e4ed8128

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeSupportMetadata
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleKeys
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleColors
import Theorems.Thm_QEC_Coding_BDL26NativeTriangleColors_colors_value
import Theorems.Thm_QEC_Coding_BDL26NativeTriangleColors_row_actual
import Theorems.Thm_QEC_Coding_BDL26NativeTriangleKeys_encode_member


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26NativeTriangleColors
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26RandomPerturbation BDL26BoundedValence
open G
noncomputable section
open scoped Classical
namespace QEC.Coding.BDL26NativeTriangleColors
theorem _root_.solution (S : OddScale) (n : ℕ) (t : Triangle (P S n)) :
    nativeRow S n t∈(colorsQ S n).value := by
  rw [colors_value]
  exact List.mem_map.mpr ⟨encode S n t,BDL26NativeTriangleKeys.encode_member S n t,
    row_actual S n t⟩
end QEC.Coding.BDL26NativeTriangleColors
