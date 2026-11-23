-- Prove2me | solution 1 for PI.EF.Rect.rectClosed_mem_nhds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:27:15.669883+00:00
-- url     : https://prove2.me/submissions/eef74daf-81c0-4e82-a74a-7d0952ffe914

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_RectIntEqZeroOfDifferentiableOn
import Theorems.Thm_PI_EF_Rect_mem_rectClosed
import Theorems.Thm_PI_EF_Rect_rectOpen_eq

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
theorem _root_.solution {z w p : ℂ} (hp : p ∈ rectOpen z w) : rectClosed z w ∈ 𝓝 p := by
  have ho : IsOpen (rectOpen z w) := by
    rw [rectOpen_eq]
    exact isOpen_Ioo.reProdIm isOpen_Ioo
  refine Filter.mem_of_superset (ho.mem_nhds hp) fun s hs => ?_
  obtain ⟨h1, h2, h3, h4⟩ := hs
  exact mem_rectClosed.2 ⟨⟨h1.le, h2.le⟩, h3.le, h4.le⟩
end PI.EF.Rect
