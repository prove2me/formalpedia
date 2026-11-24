-- Prove2me | solution 1 for PositivityTheory.ThKCT.Arch.P_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:20:40.3298+00:00
-- url     : https://prove2.me/submissions/dc4cf5a1-920d-476b-988e-75f0cd30ecce

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_SmallCones_SliceArch
import Theorems.Thm_PositivityTheory_ThKCT_Arch_Bd_nonneg

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
theorem _root_.solution {m : ℕ} {f : SchwartzMap V ℂ} {C : ℝ} (h : Bd m f C) : P V m f ≤ C := by
  refine Seminorm.finset_sup_apply_le h.nonneg fun i hi => ?_
  have hi' := Finset.mem_Iic.1 hi
  refine SchwartzMap.seminorm_le_bound ℂ i.1 i.2 f h.nonneg fun x => le_trans ?_ (h i.2 hi'.2 x)
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  exact (pow_le_pow_left₀ (norm_nonneg x) (by linarith) _).trans
    (pow_le_pow_right₀ (by linarith [norm_nonneg x]) hi'.1)
end PositivityTheory.ThKCT.Arch
