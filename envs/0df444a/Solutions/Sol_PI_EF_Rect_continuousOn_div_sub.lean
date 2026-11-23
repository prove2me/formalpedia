-- Prove2me | solution 1 for PI.EF.Rect.continuousOn_div_sub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:24:13.667214+00:00
-- url     : https://prove2.me/submissions/3375fcad-0d3e-4da0-8ade-6ed37ea09746

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_RectIntEqZeroOfDifferentiableOn
import Theorems.Thm_PI_EF_Rect_ne_of_mem_bdry_of_mem_open

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
theorem _root_.solution {h : ℂ → ℂ} {z w p : ℂ} (hp : p ∈ rectOpen z w)
    (hh : ContinuousOn h (rectBdry z w)) : ContinuousOn (fun s => h s / (s - p)) (rectBdry z w) :=
  hh.div (continuousOn_id.sub continuousOn_const) fun s hs =>
    sub_ne_zero.2 (ne_of_mem_bdry_of_mem_open hs hp)
end PI.EF.Rect
