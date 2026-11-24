-- Prove2me | solution 1 for PositivityTheory.ThKCT.Arch.exists_P
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:57:49.746854+00:00
-- url     : https://prove2.me/submissions/f64b3751-2904-4bf4-bc74-6ab7ad3d0308

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
theorem _root_.solution (q : Seminorm ℂ (SchwartzMap V ℂ)) (hq : Continuous q) : ∃ (m : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ f, q f ≤ C * P V m f := by
  obtain ⟨s, C, -, h⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ V ℂ) q hq
  refine ⟨s.sup fun i => max i.1 i.2, C, C.2, fun f => (h f).trans ?_⟩
  rw [Seminorm.smul_apply, NNReal.smul_def, smul_eq_mul]
  refine mul_le_mul_of_nonneg_left (Seminorm.finset_sup_apply_le (apply_nonneg _ _) fun i hi => ?_) C.2
  have := Finset.le_sup (f := fun i : ℕ × ℕ => max i.1 i.2) hi
  exact Seminorm.le_finset_sup_apply (Finset.mem_Iic.2 ⟨(le_max_left _ _).trans this, (le_max_right _ _).trans this⟩)
end PositivityTheory.ThKCT.Arch
