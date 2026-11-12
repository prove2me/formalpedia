-- Prove2me | solution 1 for QEC.Coding.BDL26NativeTriangleKeys.invalid_copy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T02:05:04.371312+00:00
-- url     : https://prove2.me/submissions/f9ca5432-8fd4-40bb-81d7-ec1b0e96860f

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_NativePresentationGenerator
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleKeys
import Theorems.Thm_QEC_Coding_BDL26NativeTriangleKeys_keyOfCode_failure

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26NativeTriangleKeys
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RandomPerturbation
open BDL26DecodingGraph
noncomputable section
namespace QEC.Coding.BDL26NativeTriangleKeys
theorem _root_.solution (S : OddScale) (n : ℕ) (c : Code) (h : 2≤c.copy) :
    (keyOfCodeQ S n c).1=none := by
  apply (keyOfCode_failure S n c).mpr
  rintro ⟨t,ht⟩
  have he := congrArg (fun c : Code => c.copy) ht
  have hd := t.2.isLt
  change t.2.val=c.copy at he
  omega
end QEC.Coding.BDL26NativeTriangleKeys
