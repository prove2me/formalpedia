-- Prove2me | solution 1 for QEC.Coding.BDL26NativeTriangleKeys.atlas_original_row
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T01:36:07.522222+00:00
-- url     : https://prove2.me/submissions/ce6190d3-acdf-4c39-ae92-3fcdc6747957

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_NativePresentationGenerator
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleKeys
import Theorems.Thm_QEC_Coding_BDL26NativeTriangleKeys_keySetup_spec
import Theorems.Thm_QEC_Coding_BDL26NativeTriangleKeys_encode_member

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26NativeTriangleKeys
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RandomPerturbation
open BDL26DecodingGraph
noncomputable section
namespace QEC.Coding.BDL26NativeTriangleKeys
theorem _root_.solution (S : OddScale) (n : ℕ) (t : Triangle (P S n)) :
    (encode S n t,(nativeTriangleIndex S n t).val)∈(keySetupQ S n).1 := by
  rw [(keySetup_spec S n).1]
  apply List.mem_map.mpr
  exact ⟨encode S n t,encode_member S n t,rfl⟩
end QEC.Coding.BDL26NativeTriangleKeys
