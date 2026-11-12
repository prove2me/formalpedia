-- Prove2me | solution 1 for QEC.Coding.BDL26NativeTriangleColors.native_bounded_value
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T02:11:00.287467+00:00
-- url     : https://prove2.me/submissions/5f4d489f-c596-4286-a28a-0035367fed1e

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
theorem _root_.solution (S : OddScale) (n : ℕ) (t : Triangle (P S n)) (i : Fin 3) :
    (nativeBoundedColor S n t i).val=nativeColor S n t i := rfl
end QEC.Coding.BDL26NativeTriangleColors
