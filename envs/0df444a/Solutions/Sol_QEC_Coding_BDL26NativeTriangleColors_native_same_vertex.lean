-- Prove2me | solution 1 for QEC.Coding.BDL26NativeTriangleColors.native_same_vertex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T02:11:44.485403+00:00
-- url     : https://prove2.me/submissions/3c6302e3-bbe0-4e61-abe2-19277ba2eb2f

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeSupportMetadata
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleKeys
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleColors
import Theorems.Thm_QEC_Coding_BDL26NativeTriangleColors_policy_same_vertex
import Theorems.Thm_QEC_Coding_BDL26NativeTriangleColors_nativeKey_injective

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26NativeTriangleColors
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26RandomPerturbation BDL26BoundedValence
open G
noncomputable section
open scoped Classical
namespace QEC.Coding.BDL26NativeTriangleColors
theorem _root_.solution (S : OddScale) (n : ℕ) {a b : Triangle (P S n)}
    (hc : nativeColor S n a=nativeColor S n b) {i j : Fin 3}
    (hv : triangleVertex (P S n) a i=triangleVertex (P S n) b j) : a=b :=
  policy_same_vertex _ _ (nativeKey_injective S n) hc hv
end QEC.Coding.BDL26NativeTriangleColors
