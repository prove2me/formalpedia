-- Prove2me | solution 1 for QEC.Coding.BDL26NativeMasterCandidates.master_accounting
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T09:12:53.221198+00:00
-- url     : https://prove2.me/submissions/5efc286f-6078-44d2-bc3e-6f1f6dc85b6d

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
theorem _root_.solution (S : OddScale) (n : ℕ) :
    (masterCandidatesQ S n).operations=(BDL26NativePresentationGenerator.setupQ S n).2+
      (quadruplesQ (candidateQ S n) (actualCodes S n)).operations+2 ∧
      (masterCandidatesQ S n).allocations=BDL26NativePresentationGenerator.allocatedRecords S n+
        (quadruplesQ (candidateQ S n) (actualCodes S n)).allocations+1 := ⟨rfl,rfl⟩
end QEC.Coding.BDL26NativeMasterCandidates
