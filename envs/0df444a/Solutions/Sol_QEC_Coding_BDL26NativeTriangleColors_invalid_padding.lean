-- Prove2me | solution 1 for QEC.Coding.BDL26NativeTriangleColors.invalid_padding
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T02:14:38.268089+00:00
-- url     : https://prove2.me/submissions/c2231938-8679-466d-83bc-bc002c80748b

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeSupportMetadata
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleKeys
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleColors
import Theorems.Thm_QEC_Coding_BDL26NativeTriangleColors_lookup_failure_iff
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26NativeTriangleColors
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26RandomPerturbation BDL26BoundedValence
open G
noncomputable section
open scoped Classical
namespace QEC.Coding.BDL26NativeTriangleColors
theorem _root_.solution (S : OddScale) (n : ℕ) (c : Code) (hl : c.l≠0) :
    (colorOfCodeQ S n c).value=none := by
  apply (lookup_failure_iff S n c).mpr
  rintro ⟨t,ht⟩
  exact hl (congrArg (fun c : Code => c.l) ht).symm
end QEC.Coding.BDL26NativeTriangleColors
