-- Prove2me | solution 1 for QEC.Coding.BDL26NativeTriangleColors.colors_order
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T08:14:38.936562+00:00
-- url     : https://prove2.me/submissions/da5dfb56-2ff2-42b2-b6ae-fa30f03cae19

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeSupportMetadata
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleKeys
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleColors
import Theorems.Thm_QEC_Coding_BDL26NativeTriangleColors_row_code
import Theorems.Thm_QEC_Coding_BDL26NativeTriangleColors_colors_value

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26NativeTriangleColors
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26RandomPerturbation BDL26BoundedValence
open G
namespace QEC.Coding.BDL26NativeTriangleColors
theorem _root_.solution (S : OddScale) (n : ℕ) :
    (colorsQ S n).value.map Prod.fst=T S n := by
  rw [colors_value,List.map_map]
  have he : (fun c => (colorRowQ (BDL26NativeSupportMetadata.atlasQ S n).value c).value.1)=id := by
    funext c
    exact row_code _ c
  change (T S n).map
    (fun c => (colorRowQ (BDL26NativeSupportMetadata.atlasQ S n).value c).value.1)=T S n
  rw [he]
  exact List.map_id _
end QEC.Coding.BDL26NativeTriangleColors
