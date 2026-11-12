-- Prove2me | solution 1 for QEC.Coding.BDL26NativeTriangleColors.native_rank_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T08:20:54.28162+00:00
-- url     : https://prove2.me/submissions/5ad5d171-e85f-4901-9279-ef2248182474

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeSupportMetadata
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleKeys
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleColors
import Theorems.Thm_QEC_Coding_BDL26BoundedValence_state_boundedValence


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26NativeTriangleColors
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26RandomPerturbation BDL26BoundedValence
open G
noncomputable section
open scoped Classical
namespace QEC.Coding.BDL26NativeTriangleColors
theorem _root_.solution (S : OddScale) (n : ℕ) (t : Triangle (P S n)) (i : Fin 3) :
    nativeColor S n t i<56 := policyColor_lt _ _ (state_boundedValence S n) t i
end QEC.Coding.BDL26NativeTriangleColors
