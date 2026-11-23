-- Prove2me | solution 1 for PI.EF.Rect.vseg_mem_bdry_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:25:36.098798+00:00
-- url     : https://prove2.me/submissions/16e73fa6-76b5-4e9b-80c1-15de6e9b4911

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
theorem _root_.solution {z w : ℂ} {y : ℝ} (hy : y ∈ uIcc z.im w.im) :
    ((z.re : ℂ) + y * I) ∈ rectBdry z w := by
  simp only [rectBdry, Set.mem_ofPred_eq]
  exact Or.inr ⟨by simpa using hy, Or.inl (by simp)⟩
end PI.EF.Rect
