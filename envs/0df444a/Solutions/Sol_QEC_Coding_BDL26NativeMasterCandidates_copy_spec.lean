-- Prove2me | solution 1 for QEC.Coding.BDL26NativeMasterCandidates.copy_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T09:09:46.682757+00:00
-- url     : https://prove2.me/submissions/c93d540e-cbaa-4a37-8fe0-c2fefd900032

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeSupportMetadata
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleKeys
import Mathlib.Data.List.Sublists
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeMasterCandidates

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26NativeMasterCandidates
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
namespace QEC.Coding.BDL26NativeMasterCandidates
theorem _root_.solution (c : Code) :
    (copyCodeQ c).value=c ∧ (copyCodeQ c).operations=21 ∧
      (copyCodeQ c).allocations=1 := by
  cases c
  exact ⟨rfl,rfl,rfl⟩
end QEC.Coding.BDL26NativeMasterCandidates
