-- Prove2me | solution 1 for PositivityTheory.ThKCT.Arch.Bd.succ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:21:12.412317+00:00
-- url     : https://prove2.me/submissions/792c27e5-d913-4f51-99ae-6705a8a3de40

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_SmallCones_SliceArch

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
theorem _root_.solution {m : ℕ} {f : V → ℂ} {C : ℝ} (h : Bd (m + 1) f C) : Bd m f C := fun j hj x =>
  le_trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by linarith [norm_nonneg x]) (Nat.le_succ m)) (norm_nonneg _))
    (h j (hj.trans (Nat.le_succ m)) x)
end Bd
end PositivityTheory.ThKCT.Arch
