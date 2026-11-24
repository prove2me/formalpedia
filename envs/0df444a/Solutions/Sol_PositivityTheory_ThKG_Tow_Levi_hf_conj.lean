-- Prove2me | solution 1 for PositivityTheory.ThKG.Tow.Levi.hf_conj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:36:50.267146+00:00
-- url     : https://prove2.me/submissions/ba9c8786-bc07-47ce-b433-7c3f6c4c3e1a

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
theorem _root_.solution (hM : ∀ i j, star (M j i) = M i j) (x y : n → ℂ) : starRingEnd ℂ (hf M x y) = hf M y x := by
  simp only [hf_apply, dotProduct, mulVec, map_sum, map_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← hM i j]
  simp [mul_comm, mul_left_comm]
end PositivityTheory.ThKG.Tow.Levi
