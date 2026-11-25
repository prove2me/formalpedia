-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.scaled_circle_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:05:34.822488+00:00
-- url     : https://prove2.me/submissions/1e9d944b-040d-4aa9-b805-ce0dfb9613e5

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMollA
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshBasic
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMollB

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
theorem _root_.solution {ε : ℝ} {c : ℂ} (hc : ‖c‖ = 1) (w : Fin D → ℂ) :
    ρ.scaled ε (c • w) = ρ.scaled ε w := by
  simp only [Mollifier.scaled]
  rw [smul_comm, ρ.circle_inv c _ hc]
end ReciprocityTheory.AnForm.A
