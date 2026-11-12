-- Prove2me | solution 1 for QEC.Coding.BDL26NativeTriangleKeys.keySetup_nodup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T02:02:07.060224+00:00
-- url     : https://prove2.me/submissions/b603661b-d4fc-4f86-86c7-88bb0f5f5b6d

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_NativePresentationGenerator
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleKeys
import Theorems.Thm_QEC_Coding_BDL26NativeTriangleKeys_keySetup_projections

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26NativeTriangleKeys
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RandomPerturbation
open BDL26DecodingGraph
namespace QEC.Coding.BDL26NativeTriangleKeys
theorem _root_.solution (S : OddScale) (n : ℕ) :
    (keySetupQ S n).1.Nodup ∧ ((keySetupQ S n).1.map Prod.snd).Nodup := by
  have hk : ((keySetupQ S n).1.map Prod.snd).Nodup := by
    rw [(keySetup_projections S n).2]; exact List.nodup_range
  exact ⟨List.Nodup.of_map Prod.snd hk,hk⟩
end QEC.Coding.BDL26NativeTriangleKeys
