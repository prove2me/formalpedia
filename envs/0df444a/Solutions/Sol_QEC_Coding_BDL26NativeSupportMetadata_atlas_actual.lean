-- Prove2me | solution 1 for QEC.Coding.BDL26NativeSupportMetadata.atlas_actual
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T08:48:27.867645+00:00
-- url     : https://prove2.me/submissions/66d5c7c8-1547-43f5-ad56-eadac1225cdb

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeStateRows
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeSupportMetadata
import Theorems.Thm_QEC_Coding_BDL26NativeSupportMetadata_atlas_read_map
import Theorems.Thm_QEC_Coding_BDL26NativeSupportMetadata_atlas_value
import Theorems.Thm_QEC_Coding_BDL26NativeSupportMetadata_triangle_member
import Theorems.Thm_QEC_Coding_BDL26NativeSupportMetadata_endpoint_actual
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26NativeSupportMetadata
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open N
noncomputable section
open scoped Classical
namespace QEC.Coding.BDL26NativeSupportMetadata
theorem _root_.solution (S : OddScale) (n : ℕ) (t : Triangle (P S n)) :
    (atlasReadQ (triangleCode S n t) (atlasQ S n).value).value=some (corners S n t) := by
  rw [atlas_value]
  exact (atlas_read_map _ _ _ (triangle_member S n t)).trans (endpoint_actual S n t)
end QEC.Coding.BDL26NativeSupportMetadata
