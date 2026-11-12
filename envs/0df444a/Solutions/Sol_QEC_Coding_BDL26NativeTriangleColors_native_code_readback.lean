-- Prove2me | solution 1 for QEC.Coding.BDL26NativeTriangleColors.native_code_readback
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T02:10:51.851779+00:00
-- url     : https://prove2.me/submissions/eee0162b-73cc-4570-8252-1ef3f2a830b1

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeSupportMetadata
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleKeys
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleColors
import Theorems.Thm_QEC_Coding_BDL26NativeTriangleKeys_encode_readback


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26NativeTriangleColors
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26RandomPerturbation BDL26BoundedValence
open G
noncomputable section
open scoped Classical
namespace QEC.Coding.BDL26NativeTriangleColors
theorem _root_.solution (S : OddScale) (n : ℕ) (t : Triangle (P S n)) :
    nativeKey S n t=2*(encode S n t).owner+(encode S n t).copy ∧
      BDL26NativeTriangleKeys.codeAtKey (nativeKey S n t)=encode S n t :=
  ⟨rfl,BDL26NativeTriangleKeys.encode_readback S n t⟩
end QEC.Coding.BDL26NativeTriangleColors
