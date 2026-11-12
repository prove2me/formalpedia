-- Prove2me | solution 1 for QEC.Coding.BDL26NativeMasterCandidates.master_count
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T09:14:44.946201+00:00
-- url     : https://prove2.me/submissions/da2c9fce-2e2a-4aa9-bbfc-5c78404e097a

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeSupportMetadata
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleKeys
import Mathlib.Data.List.Sublists
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeMasterCandidates
import Theorems.Thm_QEC_Coding_BDL26NativeMasterCandidates_quadruples_count

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26NativeMasterCandidates
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
namespace QEC.Coding.BDL26NativeMasterCandidates
theorem _root_.solution (S : OddScale) (n : ℕ) :
    (Rows S n).length=Nat.choose (actualCodes S n).length 4 := by
  rw [master_value,List.length_map,quadruples_count]
end QEC.Coding.BDL26NativeMasterCandidates
