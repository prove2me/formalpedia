-- Prove2me | solution 1 for QEC.Coding.BDL26NativeTriangleKeys.seed_keys
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T02:02:36.81061+00:00
-- url     : https://prove2.me/submissions/7daa7b50-c864-4005-af8b-cf2f6be93250

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_NativePresentationGenerator
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleKeys
import Theorems.Thm_QEC_Coding_BDL26NativeTriangleKeys_keySetup_projections

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26NativeTriangleKeys
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RandomPerturbation
open BDL26DecodingGraph
namespace QEC.Coding.BDL26NativeTriangleKeys
theorem _root_.solution (S : OddScale) :
    ((keySetupQ S 0).1.map Prod.snd)=List.range 8 := by
  rw [(keySetup_projections S 0).2,triangle_count]
  rfl
end QEC.Coding.BDL26NativeTriangleKeys
