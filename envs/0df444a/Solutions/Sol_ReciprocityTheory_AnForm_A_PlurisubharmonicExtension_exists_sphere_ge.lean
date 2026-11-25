-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.PlurisubharmonicExtension.exists_sphere_ge
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:03:36.520316+00:00
-- url     : https://prove2.me/submissions/30aa0acb-1d55-43af-9e08-e073970988ad

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshPoisson
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshExtA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Metric Real Filter Topology MeasureTheory
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A ReciprocityTheory.AnForm.A.PlurisubharmonicExtension
namespace ReciprocityTheory.AnForm.A.PlurisubharmonicExtension
theorem _root_.solution {g : ℂ → ℝ} {r : ℝ} (hr : 0 < r)
    (hc : ContinuousOn g (sphere 0 r)) (h : g 0 ≤ circleAverage g 0 r) :
    ∃ ζ ∈ sphere (0 : ℂ) r, g 0 ≤ g ζ := by
  by_contra hno
  push Not at hno
  obtain ⟨ζ1, hζ1, hmax⟩ := (isCompact_sphere (0 : ℂ) r).exists_isMaxOn
    (NormedSpace.sphere_nonempty.2 hr.le) hc
  have hle : circleAverage g 0 r ≤ g ζ1 := by
    apply circleAverage_mono_on_of_le_circle
    · exact hc.circleIntegrable hr.le
    · intro x hx
      rw [abs_of_pos hr] at hx
      exact hmax hx
  linarith [hno ζ1 hζ1]
end ReciprocityTheory.AnForm.A.PlurisubharmonicExtension
