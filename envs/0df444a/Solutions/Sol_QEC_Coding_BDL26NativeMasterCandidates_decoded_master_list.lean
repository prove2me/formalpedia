-- Prove2me | solution 1 for QEC.Coding.BDL26NativeMasterCandidates.decoded_master_list
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T09:24:30.854829+00:00
-- url     : https://prove2.me/submissions/b3d08285-b9e6-411e-86aa-8e7863e8630c

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeSupportMetadata
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleKeys
import Mathlib.Data.List.Sublists
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeMasterCandidates
import Theorems.Thm_QEC_Coding_BDL26NativeMasterCandidates_master_nodup
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26NativeMasterCandidates
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
noncomputable section
open scoped Classical
namespace QEC.Coding.BDL26NativeMasterCandidates
theorem _root_.solution (S : OddScale) (n : ℕ) :
    (decodedMasters S n).Nodup ∧ (decodedMasters S n).toFinset=Finset.univ := by
  constructor
  · exact (master_nodup S n).1.attach.map (masterEquiv S n).injective
  · apply Finset.eq_univ_of_forall
    intro m
    let row := (masterEquiv S n).symm m
    apply List.mem_toFinset.mpr
    exact List.mem_map.mpr ⟨row,List.mem_attach _ _,(masterEquiv S n).apply_symm_apply m⟩
end QEC.Coding.BDL26NativeMasterCandidates
