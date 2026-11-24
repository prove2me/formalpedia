-- Prove2me | solution 1 for PositivityTheory.ThKCT.Arch.Bd.shift
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:15:04.844095+00:00
-- url     : https://prove2.me/submissions/2c467999-a799-49f3-bfb3-b64266e2759c

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_SmallCones_SliceArch
import Theorems.Thm_PositivityTheory_ThKCT_Arch_peetre

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKCT PositivityTheory.ThKCT.Arch
open scoped ContDiff NNReal
open Complex Filter Topology
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
namespace PositivityTheory.ThKCT.Arch
namespace Bd
theorem _root_.solution {m : ℕ} {f : V → ℂ} {C : ℝ} (h : Bd m f C) (t : V) : Bd m (fun x => f (x + t)) ((1 + ‖t‖) ^ m * C) := by
  intro j hj x
  rw [iteratedFDeriv_comp_add_right]
  refine le_trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity)
    (peetre x (x + t) (r := ‖t‖) (by simp)) m) (norm_nonneg _)) ?_
  rw [mul_pow, mul_assoc]
  exact mul_le_mul_of_nonneg_left (h j hj _) (by positivity)
end Bd
end PositivityTheory.ThKCT.Arch
