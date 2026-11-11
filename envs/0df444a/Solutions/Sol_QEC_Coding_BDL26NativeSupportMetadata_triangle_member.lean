-- Prove2me | solution 1 for QEC.Coding.BDL26NativeSupportMetadata.triangle_member
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T05:46:17.997056+00:00
-- url     : https://prove2.me/submissions/8707641c-4e53-4b04-ad42-73c6aa6cd04e

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeStateRows
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeSupportMetadata
import Theorems.Thm_QEC_Coding_BDL26NativePresentationGenerator_triangle_labels


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
    triangleCode S n t∈T S n :=
  (BDL26NativePresentationGenerator.triangle_labels S n _).mpr ⟨t,rfl⟩
end QEC.Coding.BDL26NativeSupportMetadata
