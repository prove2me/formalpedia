-- Prove2me | solution 1 for QEC.Coding.BDL26NativeSupportMetadata.query_invalid_padding
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T01:58:57.929815+00:00
-- url     : https://prove2.me/submissions/7cf4ed65-0144-4d47-86ae-93c3ee2ccb51

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeStateRows
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeSupportMetadata
import Theorems.Thm_QEC_Coding_BDL26NativeSupportMetadata_query_missing
import Theorems.Thm_QEC_Coding_BDL26NativePresentationGenerator_triangle_labels
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


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
theorem _root_.solution (S : OddScale) (n : ℕ) (codes : FourCodes)
    (hl : codes.first.l≠0) : (queryQ S n codes).value=none := by
  apply query_missing S n codes
  intro hc
  obtain ⟨t,ht⟩ := (BDL26NativePresentationGenerator.triangle_labels S n codes.first).mp hc
  exact hl (congrArg (fun c : Code => c.l) ht).symm
end QEC.Coding.BDL26NativeSupportMetadata
