-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.exists_thick
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:48:33.876661+00:00
-- url     : https://prove2.me/submissions/c1a88b37-299e-4205-8031-7f5c92f1bda4

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
theorem _root_.solution (hU : IsOpen U) {ε : ℝ} (hε : 0 ≤ ε) {z : Fin D → ℂ} (hz : z ∈ shrink U ε) :
    ∃ δ > 0, closedBall z (ε + δ) ⊆ U := by
  obtain ⟨δ, hδ, h⟩ := (isCompact_closedBall z ε).exists_cthickening_subset_open hU hz
  rw [cthickening_closedBall hδ.le hε] at h
  exact ⟨δ, hδ, by rw [add_comm]; exact h⟩
end ReciprocityTheory.AnForm.A
