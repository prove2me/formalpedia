-- Prove2me | solution 1 for PositivityTheory.ThKG.Tow.Levi.iso_of_hf
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:22:28.857487+00:00
-- url     : https://prove2.me/submissions/931c8e1d-6bdc-4c0e-ab76-bcdb9b34ecdd

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_TowerModels_ExistsRefl
import Theorems.Thm_PositivityTheory_ThKG_Tow_Levi_hf_apply
import Theorems.Thm_PositivityTheory_ThKG_Tow_Levi_hf_mulVec

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
namespace PositivityTheory.ThKG.Tow.Levi
theorem _root_.solution {g : Matrix n n ℂ} (h : ∀ x y, hf M (g *ᵥ x) (g *ᵥ y) = hf M x y) : gᵀ * M * g.map star = M := by
  ext i j
  have := h (Pi.single i 1) (Pi.single j 1)
  rw [hf_mulVec, hf_apply, hf_apply] at this
  simpa [← Pi.single_star] using this
end PositivityTheory.ThKG.Tow.Levi
