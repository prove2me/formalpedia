-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.scaled_hasCompactSupport
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:15:00.157311+00:00
-- url     : https://prove2.me/submissions/87c5aed6-5aac-4643-b1b8-a8ed73ebda05

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
theorem _root_.solution {ε : ℝ} (hε : 0 < ε) : HasCompactSupport (ρ.scaled ε) :=
  HasCompactSupport.intro (isCompact_closedBall 0 ε) fun _ hw =>
    scaled_eq_zero ρ hε (le_of_lt (not_le.1 fun h => hw (mem_closedBall_zero_iff.2 h)))
end ReciprocityTheory.AnForm.A
