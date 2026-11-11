-- Prove2me | solution 1 for QEC.Coding.BDL26NativeTriangleKeys.keyOfCode_original
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T01:38:12.600384+00:00
-- url     : https://prove2.me/submissions/b2800a8c-9c30-47de-951d-b742e67bc946

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_NativePresentationGenerator
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleKeys
import Theorems.Thm_QEC_Coding_BDL26NativeTriangleKeys_encode_member
import Theorems.Thm_QEC_Coding_BDL26NativeTriangleKeys_keyOfCode_value

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26NativeTriangleKeys
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RandomPerturbation
open BDL26DecodingGraph
noncomputable section
namespace QEC.Coding.BDL26NativeTriangleKeys
theorem _root_.solution (S : OddScale) (n : ℕ) (t : Triangle (P S n)) :
    (keyOfCodeQ S n (encode S n t)).1=some (nativeTriangleIndex S n t).val := by
  rw [keyOfCode_value,if_pos (encode_member S n t)]
  rfl
end QEC.Coding.BDL26NativeTriangleKeys
