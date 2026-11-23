-- Prove2me | solution 1 for PI.EF.Rect.hseg_mem_bdry_top
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:25:35.588297+00:00
-- url     : https://prove2.me/submissions/3ba5e3d5-a0f3-4688-88c1-8dfc31dfc909

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_RectIntEqZeroOfDifferentiableOn

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
theorem _root_.solution {z w : ℂ} {x : ℝ} (hx : x ∈ uIcc z.re w.re) :
    ((x : ℂ) + w.im * I) ∈ rectBdry z w := by
  simp only [rectBdry, Set.mem_ofPred_eq]
  exact Or.inl ⟨by simpa using hx, Or.inr (by simp)⟩
end PI.EF.Rect
