-- Prove2me | solution 1 for PI.EF.Rect.ne_of_mem_bdry_of_mem_open
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:25:33.255922+00:00
-- url     : https://prove2.me/submissions/cd166c5b-7e59-44a2-b1e7-eac18ad18c61

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
theorem _root_.solution {z w s p : ℂ} (hs : s ∈ rectBdry z w) (hp : p ∈ rectOpen z w) :
    s ≠ p := by
  rintro rfl
  obtain ⟨h1, h2, h3, h4⟩ := hp
  rcases hs with ⟨-, h | h⟩ | ⟨-, h | h⟩ <;> linarith
end PI.EF.Rect
