-- Prove2me | solution 1 for PI.EF.Rect.rectBdry_subset
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:27:06.241138+00:00
-- url     : https://prove2.me/submissions/47ed9792-157b-46d6-8665-7b7c6c1479b2

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_RectIntEqZeroOfDifferentiableOn
import Theorems.Thm_PI_EF_Rect_mem_rectClosed

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.EF PI.EF.Rect
open Complex MeasureTheory intervalIntegral Set Filter Topology Real
namespace PI.EF.Rect
theorem _root_.solution {z w : ℂ} (hre : z.re ≤ w.re) (him : z.im ≤ w.im) :
    rectBdry z w ⊆ rectClosed z w := by
  intro s hs
  rw [mem_rectClosed]
  rcases hs with ⟨hr, hi⟩ | ⟨hi, hr⟩
  · rw [uIcc_of_le hre, Set.mem_Icc] at hr
    rcases hi with hi | hi <;> exact ⟨hr, by constructor <;> linarith⟩
  · rw [uIcc_of_le him, Set.mem_Icc] at hi
    rcases hr with hr | hr <;> exact ⟨by constructor <;> linarith, hi⟩
end PI.EF.Rect
