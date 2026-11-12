-- Prove2me | solution 1 for QEC.Coding.BDL26NativeTriangleColors.native_support_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T02:12:14.894271+00:00
-- url     : https://prove2.me/submissions/35318a93-58a4-44d0-a208-b90edc1e3586

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeSupportMetadata
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleKeys
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleColors
import Theorems.Thm_QEC_Coding_BDL26NativeTriangleColors_policy_support_disjoint
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
    (hne : a≠b) (hc : nativeColor S n a=nativeColor S n b) :
    Disjoint (triangleSupport (P S n) a) (triangleSupport (P S n) b) :=
  policy_support_disjoint _ _ (nativeKey_injective S n) hne hc
end QEC.Coding.BDL26NativeTriangleColors
