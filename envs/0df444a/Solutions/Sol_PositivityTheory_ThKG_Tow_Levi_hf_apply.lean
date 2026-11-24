-- Prove2me | solution 1 for PositivityTheory.ThKG.Tow.Levi.hf_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:23:44.306629+00:00
-- url     : https://prove2.me/submissions/59acbf77-ff4c-4876-9dea-bcb3c7ff80b6

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_TowerModels_ExistsRefl

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
theorem _root_.solution (x y : n → ℂ) : hf M x y = x ⬝ᵥ M *ᵥ star y := rfl
end PositivityTheory.ThKG.Tow.Levi
