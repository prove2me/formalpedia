-- Prove2me | solution 1 for QEC.Coding.BDL26NativeTriangleKeys.keySetup_range
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T02:02:24.177276+00:00
-- url     : https://prove2.me/submissions/ca2a4d34-0d85-4d30-a800-966b67b10617

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_NativePresentationGenerator
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleKeys
import Theorems.Thm_QEC_Coding_BDL26NativeTriangleKeys_keySetup_projections

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26NativeTriangleKeys
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RandomPerturbation
open BDL26DecodingGraph
namespace QEC.Coding.BDL26NativeTriangleKeys
theorem _root_.solution (S : OddScale) (n : ℕ) (k : ℕ) :
    k∈((keySetupQ S n).1.map Prod.snd) ↔ k<triangleCount S n := by
  rw [(keySetup_projections S n).2]; exact List.mem_range
end QEC.Coding.BDL26NativeTriangleKeys
