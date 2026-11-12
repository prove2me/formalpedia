-- Prove2me | solution 1 for QEC.Coding.BDL26NativeSupportMetadata.atlas_value
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T07:57:43.853195+00:00
-- url     : https://prove2.me/submissions/52b4ab62-b3d7-49c8-91f0-28ac45a620dc

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeStateRows
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeSupportMetadata
import Theorems.Thm_QEC_Coding_BDL26NativeSupportMetadata_atlas_rows_value

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26NativeSupportMetadata
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open N
namespace QEC.Coding.BDL26NativeSupportMetadata
theorem _root_.solution (S : OddScale) (n : ℕ) :
    (atlasQ S n).value=(T S n).map (fun c => (c,(endpointQ (F S n) (V S n) (T S n) c).value)) :=
  atlas_rows_value _ _ _
end QEC.Coding.BDL26NativeSupportMetadata
