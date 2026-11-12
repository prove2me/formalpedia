-- Prove2me | solution 1 for QEC.Coding.BDL26NativeSupportMetadata.atlas_rows_value
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T07:51:09.053212+00:00
-- url     : https://prove2.me/submissions/c684e1f4-9081-40eb-bc23-1b9ad71f87f4

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeStateRows
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeSupportMetadata
import Theorems.Thm_QEC_Coding_BDL26NativeStateRows_map_value


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26NativeSupportMetadata
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open N
namespace QEC.Coding.BDL26NativeSupportMetadata
theorem _root_.solution (F : Frame) (V triangles : List Code) :
    (atlasRowsQ F V triangles).value=
      triangles.map (fun c => (c,(endpointQ F V triangles c).value)) := by
  exact BDL26NativeStateRows.map_value _ _
end QEC.Coding.BDL26NativeSupportMetadata
