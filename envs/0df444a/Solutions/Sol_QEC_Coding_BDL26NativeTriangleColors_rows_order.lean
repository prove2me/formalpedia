-- Prove2me | solution 1 for QEC.Coding.BDL26NativeTriangleColors.rows_order
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T02:09:50.655138+00:00
-- url     : https://prove2.me/submissions/40eec6ad-4972-484b-a2d1-f16d21d8c695

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeSupportMetadata
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleKeys
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleColors
import Theorems.Thm_QEC_Coding_BDL26NativeTriangleColors_row_code
import Theorems.Thm_QEC_Coding_BDL26NativeStateRows_map_value


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26NativeTriangleColors
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26RandomPerturbation BDL26BoundedValence
open G
namespace QEC.Coding.BDL26NativeTriangleColors
theorem _root_.solution {A : Type*} [DecidableEq A] (L : List (AtlasRow A)) :
    (colorRowsQ L).value.map Prod.fst=L.map Prod.fst := by
  rw [colorRowsQ,BDL26NativeStateRows.map_value,List.map_map]
  apply List.map_congr_left
  intro r _
  exact row_code L r.1
end QEC.Coding.BDL26NativeTriangleColors
