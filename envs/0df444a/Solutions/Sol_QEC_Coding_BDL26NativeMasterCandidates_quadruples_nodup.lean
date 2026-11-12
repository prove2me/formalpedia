-- Prove2me | solution 1 for QEC.Coding.BDL26NativeMasterCandidates.quadruples_nodup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T09:10:13.085425+00:00
-- url     : https://prove2.me/submissions/19c5b8fd-0446-4f22-92ec-c6b964eb83da

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
theorem _root_.solution {A : Type*} (L : List A) (h : L.Nodup) :
    (quadruples L).Nodup := by
  apply List.Nodup.of_map quadList
  rw [quadruples_lists]
  exact List.nodup_reverse.mpr (List.nodup_sublistsLen 4 h)
end QEC.Coding.BDL26NativeMasterCandidates
