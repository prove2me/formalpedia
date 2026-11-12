-- Prove2me | solution 1 for QEC.Coding.BDL26NativeTriangleKeys.invalid_family
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T02:04:37.047768+00:00
-- url     : https://prove2.me/submissions/1c0f2561-f262-4713-b38b-1c174f456799

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_NativePresentationGenerator
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleKeys
import Theorems.Thm_QEC_Coding_BDL26NativeTriangleKeys_keyOfCode_failure
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26NativeTriangleKeys
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RandomPerturbation
open BDL26DecodingGraph
noncomputable section
namespace QEC.Coding.BDL26NativeTriangleKeys
theorem _root_.solution (S : OddScale) (n : ℕ) (c : Code) (h : c.family≠3) :
    (keyOfCodeQ S n c).1=none := by
  apply (keyOfCode_failure S n c).mpr
  rintro ⟨t,ht⟩
  exact h (congrArg (fun c : Code => c.family) ht).symm
end QEC.Coding.BDL26NativeTriangleKeys
