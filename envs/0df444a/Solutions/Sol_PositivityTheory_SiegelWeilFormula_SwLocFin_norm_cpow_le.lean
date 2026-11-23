-- Prove2me | solution 1 for PositivityTheory.SiegelWeilFormula.SwLocFin.norm_cpow_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:55:36.166438+00:00
-- url     : https://prove2.me/submissions/2311dd13-f5d2-49f6-8222-fb9b8c5302ec

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_LocalCharacterIntegrals_DifferentiableSetIntegralFz

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.SwLocFin
open MeasureTheory Filter Topology Set
variable {H : Type*} [MeasurableSpace H]
namespace PositivityTheory.SiegelWeilFormula.SwLocFin
theorem _root_.solution {x : ℝ} (hx : 1 ≤ x) {R : ℝ} (hR : x ≤ R) (w : ℂ) :
    ‖(x : ℂ) ^ w‖ ≤ R ^ max w.re 0 := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (by linarith)]
  calc x ^ w.re ≤ x ^ max w.re 0 := Real.rpow_le_rpow_of_exponent_le hx (le_max_left _ _)
    _ ≤ R ^ max w.re 0 := Real.rpow_le_rpow (by linarith) hR (le_max_right _ _)
end PositivityTheory.SiegelWeilFormula.SwLocFin
