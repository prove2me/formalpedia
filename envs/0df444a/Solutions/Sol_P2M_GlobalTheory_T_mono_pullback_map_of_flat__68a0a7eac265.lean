-- Prove2me | solution 1 for P2M_GlobalTheory_T_mono_pullback_map_of_flat__68a0a7eac265
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:58:17.476586+00:00
-- url     : https://prove2.me/submissions/cb371988-cb60-4e68-8a4f-42ecea717f06

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MonoPullbackMapOfFlat
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MonoPullbackMapOfFlatStatement
import Theorems.Thm_GlobalTheory_mono_pullback_map_of_flat


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (X Y : Scheme.{0}) (f : X ⟶ Y) [Flat f] (G G' : Y.Modules) (φ : G ⟶ G') [Mono φ], Mono ((Scheme.Modules.pullback f).map φ) := by
  first | exact @GlobalTheory.mono_pullback_map_of_flat | exact GlobalTheory.mono_pullback_map_of_flat | (intros; apply GlobalTheory.mono_pullback_map_of_flat <;> assumption)
end _root_.GlobalTheory.T
