-- Prove2me | solution 1 for QEC.Coding.BDL26NativeMasterCandidates.master_bijection
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T09:04:39.811209+00:00
-- url     : https://prove2.me/submissions/a6b33715-15bd-436a-b680-66c86309da3d

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeSupportMetadata
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleKeys
import Mathlib.Data.List.Sublists
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeMasterCandidates
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
    (∀row,(masterEquiv S n).symm (masterEquiv S n row)=row) ∧
      (∀m,masterEquiv S n ((masterEquiv S n).symm m)=m) ∧
      ∀row,Rep S n row.val.1 (masterEquiv S n row) :=
  ⟨(masterEquiv S n).symm_apply_apply,(masterEquiv S n).apply_symm_apply,decodeRow_rep S n⟩
end QEC.Coding.BDL26NativeMasterCandidates
