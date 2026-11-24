-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.norm_lt_of_scaled_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:15:00.701581+00:00
-- url     : https://prove2.me/submissions/e1554662-9e1b-4af1-9372-6dcf615f8982

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMollA
import Theorems.Thm_ReciprocityTheory_AnForm_A_scaled_eq_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory Metric Filter Topology Set
open scoped ContDiff Convolution
noncomputable section
variable {D : ℕ}
variable (ρ : Mollifier D)
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution {ε : ℝ} (hε : 0 < ε) {w : Fin D → ℂ} (hw : ρ.scaled ε w ≠ 0) :
    ‖w‖ < ε :=
  lt_of_not_ge fun h => hw (scaled_eq_zero ρ hε h)
end ReciprocityTheory.AnForm.A
