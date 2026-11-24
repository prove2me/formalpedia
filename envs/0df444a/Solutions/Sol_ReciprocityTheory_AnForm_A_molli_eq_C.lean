-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.molli_eq_C
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:27:39.491132+00:00
-- url     : https://prove2.me/submissions/f34030e6-8984-4b15-90d4-4665245336ce

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMollA
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshBasic
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMollB
import Theorems.Thm_ReciprocityTheory_AnForm_A_molli_congr


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory Metric Filter Topology Set Real
open scoped ContDiff
noncomputable section
variable {D : ℕ}
variable (ρ : Mollifier D) {U : Set (Fin D → ℂ)} {φ : (Fin D → ℂ) → ℝ}
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution {ε : ℝ} (hε : 0 < ε) {C : Set (Fin D → ℂ)} {z : Fin D → ℂ}
    (hz : closedBall z ε ⊆ C) :
    molli ρ ε φ z = ∫ y, ρ.scaled ε y * C.indicator φ (z - y) := by
  rw [molli_congr ρ hε (U := C) hz (fun x hx => (indicator_of_mem hx φ).symm)]
  rfl
end ReciprocityTheory.AnForm.A
