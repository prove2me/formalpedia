-- Prove2me | solution 1 for PositivityTheory.ThKG.Tow.Levi.hf_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:34:13.649137+00:00
-- url     : https://prove2.me/submissions/cc164436-6f29-4aa5-a10a-f8cfc0371af5

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_TowerModels_ExistsRefl
import Theorems.Thm_PositivityTheory_ThKG_Tow_Levi_hf_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory PositivityTheory.ThKG PositivityTheory.ThKG.Tow PositivityTheory.ThKG.Tow.Levi
open Matrix
variable {n : Type} [Fintype n] [DecidableEq n]
variable {M θ : Matrix n n ℂ}
omit [DecidableEq n]
namespace PositivityTheory.ThKG.Tow.Levi
theorem _root_.solution (g : Matrix n n ℂ) (x y : n → ℂ) : hf M (g *ᵥ x) (g *ᵥ y) = hf (gᵀ * M * g.map star) x y := by
  have e : star (g *ᵥ y) = g.map star *ᵥ star y := funext fun i => RingHom.map_mulVec (starRingEnd ℂ) g y i
  rw [hf_apply, hf_apply, e, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec x, vecMul_transpose]
end PositivityTheory.ThKG.Tow.Levi
