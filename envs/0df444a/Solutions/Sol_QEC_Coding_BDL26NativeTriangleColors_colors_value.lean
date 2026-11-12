-- Prove2me | solution 1 for QEC.Coding.BDL26NativeTriangleColors.colors_value
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T08:07:53.776178+00:00
-- url     : https://prove2.me/submissions/c00ed8cd-80a8-442a-a26e-8022eff2252d

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeSupportMetadata
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleKeys
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleColors
import Theorems.Thm_QEC_Coding_BDL26NativeStateRows_map_value
import Theorems.Thm_QEC_Coding_BDL26NativeSupportMetadata_atlas_value


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26NativeTriangleColors
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26RandomPerturbation BDL26BoundedValence
open G
namespace QEC.Coding.BDL26NativeTriangleColors
theorem _root_.solution (S : OddScale) (n : ℕ) :
    (colorsQ S n).value=(T S n).map
      (fun c => (colorRowQ (BDL26NativeSupportMetadata.atlasQ S n).value c).value) := by
  change (colorRowsQ _).value=_
  rw [colorRowsQ,BDL26NativeStateRows.map_value,BDL26NativeSupportMetadata.atlas_value,
    List.map_map]
  rfl
end QEC.Coding.BDL26NativeTriangleColors
