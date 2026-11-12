-- Prove2me | solution 1 for QEC.Coding.BDL26NativeMasterCandidates.master_count_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T02:22:05.4882+00:00
-- url     : https://prove2.me/submissions/8b73ea78-ae4b-405a-8d57-e44c08f9b940

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeSupportMetadata
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleKeys
import Mathlib.Data.List.Sublists
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeMasterCandidates
import Theorems.Thm_QEC_Coding_BDL26NativeMasterCandidates_master_count

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26NativeMasterCandidates
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
namespace QEC.Coding.BDL26NativeMasterCandidates
theorem _root_.solution (S : OddScale) (n : ℕ) :
    (Rows S n).length≤(actualCodes S n).length^4 := by
  rw [master_count]
  exact Nat.choose_le_pow _ _
end QEC.Coding.BDL26NativeMasterCandidates
