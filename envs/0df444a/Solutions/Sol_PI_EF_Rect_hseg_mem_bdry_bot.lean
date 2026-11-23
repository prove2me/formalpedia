-- Prove2me | solution 1 for PI.EF.Rect.hseg_mem_bdry_bot
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:25:34.886315+00:00
-- url     : https://prove2.me/submissions/6a9d0b9b-db98-4e19-9bc8-ae690fa20239

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
    ((x : ℂ) + z.im * I) ∈ rectBdry z w := by
  simp only [rectBdry, Set.mem_ofPred_eq]
  exact Or.inl ⟨by simpa using hx, Or.inl (by simp)⟩
end PI.EF.Rect
