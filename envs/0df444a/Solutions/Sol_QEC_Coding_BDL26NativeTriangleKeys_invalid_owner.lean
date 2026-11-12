-- Prove2me | solution 1 for QEC.Coding.BDL26NativeTriangleKeys.invalid_owner
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T02:05:18.410638+00:00
-- url     : https://prove2.me/submissions/651be070-91db-44c8-9436-67b0ea8f5f3d

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_NativePresentationGenerator
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleKeys
import Theorems.Thm_QEC_Coding_BDL26NativeTriangleKeys_keyOfCode_failure

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26NativeTriangleKeys
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RandomPerturbation
open BDL26DecodingGraph
noncomputable section
namespace QEC.Coding.BDL26NativeTriangleKeys
theorem _root_.solution (S : OddScale) (n : ℕ) (c : Code)
    (h : (BDL26NativePresentationGenerator.setupQ S n).1.data.frame.nf≤c.owner) :
    (keyOfCodeQ S n c).1=none := by
  apply (keyOfCode_failure S n c).mpr
  rintro ⟨t,ht⟩
  have he := congrArg (fun c : Code => c.owner) ht
  have hf := ((BDL26NativePresentationGenerator.generatedRefines S n).fIndex t.1).isLt
  change ((BDL26NativePresentationGenerator.generatedRefines S n).fIndex t.1).val=c.owner at he
  change (BDL26NativePresentationGenerator.generateQ S n).1.nf≤c.owner at h
  omega
end QEC.Coding.BDL26NativeTriangleKeys
