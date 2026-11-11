-- Prove2me | solution 1 for QEC.Coding.BDL26NativeTriangleColors.nativeKey_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T04:26:30.275635+00:00
-- url     : https://prove2.me/submissions/cd09becd-095d-4ab8-95e4-d97176dad8fe

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeSupportMetadata
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleKeys
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleColors

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26NativeTriangleColors
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26RandomPerturbation BDL26BoundedValence
open G
noncomputable section
open scoped Classical
namespace QEC.Coding.BDL26NativeTriangleColors
theorem _root_.solution (S : OddScale) (n : ℕ) : Function.Injective (nativeKey S n) := by
  intro a b h
  exact (BDL26NativeTriangleKeys.nativeTriangleIndex S n).injective (Fin.ext h)
end QEC.Coding.BDL26NativeTriangleColors
