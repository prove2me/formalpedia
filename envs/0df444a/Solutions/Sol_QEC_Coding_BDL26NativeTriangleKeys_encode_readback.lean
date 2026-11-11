-- Prove2me | solution 1 for QEC.Coding.BDL26NativeTriangleKeys.encode_readback
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T01:36:18.893205+00:00
-- url     : https://prove2.me/submissions/4282cf33-4217-4390-b500-42f289122676

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_NativePresentationGenerator
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleKeys
import Theorems.Thm_QEC_Coding_BDL26NativeTriangleKeys_index_value

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26NativeTriangleKeys
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RandomPerturbation
open BDL26DecodingGraph
noncomputable section
namespace QEC.Coding.BDL26NativeTriangleKeys
theorem _root_.solution (S : OddScale) (n : ℕ) (t : Triangle (P S n)) :
    codeAtKey (nativeTriangleIndex S n t).val=encode S n t := by
  unfold codeAtKey encode
  rw [index_value]
  have hd := t.2.isLt
  congr <;> omega
end QEC.Coding.BDL26NativeTriangleKeys
