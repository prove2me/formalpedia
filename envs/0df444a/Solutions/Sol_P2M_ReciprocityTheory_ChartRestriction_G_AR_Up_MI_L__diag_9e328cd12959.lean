-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_MI_L__diag_9e328cd12959
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:06:42.271915+00:00
-- url     : https://prove2.me/submissions/64e758f2-30e5-47c2-8f69-69ad5da6afe8

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_MeasInvStatementPfD
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_MeasInvStatementPfE

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.MI
open Matrix MeasureTheory
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.MI
theorem _root_.solution (β : ι → Matrix (Fin r) (Fin r) ℂ) (hβ : ∀ τ, (β τ).BlockTriangular id) (y : UpI ι r → ℂ)
    (τ : ι) (b : Fin r) : Lβ β y (dI τ b) = β τ b b * y (dI τ b) := by
  show (β τ * Umat y τ) b b = β τ b b * y (dI τ b)
  rw [Matrix.mul_apply, Finset.sum_eq_single b]
  · simp [Umat, dI]
  · intro c _ hcb
    rcases lt_or_gt_of_ne hcb with h | h
    · rw [hβ τ h, zero_mul]
    · simp [Umat, h]
  · intro h
    exact absurd (Finset.mem_univ b) h
end ReciprocityTheory.ChartRestriction.G.AR.Up.MI
