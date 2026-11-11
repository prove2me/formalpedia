-- Prove2me | solution 1 for QEC.Coding.BDL26NativeTriangleKeys.index_inverse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T01:30:14.487929+00:00
-- url     : https://prove2.me/submissions/3727ed27-c7c1-40d9-9975-f1ab495b866a

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_NativePresentationGenerator
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleKeys
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26NativeTriangleKeys
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RandomPerturbation
open BDL26DecodingGraph
noncomputable section
namespace QEC.Coding.BDL26NativeTriangleKeys
theorem _root_.solution (S : OddScale) (n : ℕ) :
    (∀t,(nativeTriangleIndex S n).symm (nativeTriangleIndex S n t)=t) ∧
      (∀k,nativeTriangleIndex S n ((nativeTriangleIndex S n).symm k)=k) :=
  ⟨(nativeTriangleIndex S n).symm_apply_apply,(nativeTriangleIndex S n).apply_symm_apply⟩
end QEC.Coding.BDL26NativeTriangleKeys
