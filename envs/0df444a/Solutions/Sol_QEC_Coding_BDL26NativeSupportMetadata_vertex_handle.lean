-- Prove2me | solution 1 for QEC.Coding.BDL26NativeSupportMetadata.vertex_handle
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T08:23:30.07453+00:00
-- url     : https://prove2.me/submissions/45d212a5-da0a-4505-90b4-7242826572a9

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeStateRows
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeSupportMetadata

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
theorem _root_.solution (S : OddScale) (n : ℕ) (v : Vertex (P S n)) :
    (BDL26NativePresentationGenerator.handleQ (vertexCode S n v) (V S n)).1=
      (BDL26NativePresentationGenerator.generatedVertexIndex S n v).val := by
  cases v <;> rfl
end QEC.Coding.BDL26NativeSupportMetadata
