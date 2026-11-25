-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.MI.hasFDerivAt_entry2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:33:43.640889+00:00
-- url     : https://prove2.me/submissions/fe4c1338-a12e-479c-9c9d-3c4b26abed40

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_MeasInvStatementPfA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.MI
open Matrix
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.MI
theorem _root_.solution (w : Ix ι r → ℂ) (τ : ι) (k b : Fin r) :
    HasFDerivAt (fun v : Ix ι r → ℂ => up v τ k b)
      (if b < k then 0 else ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Ix ι r => ℂ) (τ, k, b)) w := by
  by_cases hk : b < k
  · rw [if_pos hk]
    have hf : (fun v : Ix ι r → ℂ => up v τ k b) = fun _ => (0 : ℂ) := by
      funext v
      simp [up, hk]
    rw [hf]
    exact hasFDerivAt_const _ _
  · rw [if_neg hk]
    have hf : (fun v : Ix ι r → ℂ => up v τ k b) = fun v => v (τ, k, b) := by
      funext v
      simp [up, hk]
    rw [hf]
    exact hasFDerivAt_apply (𝕜 := ℝ) (τ, k, b) w
end ReciprocityTheory.ChartRestriction.G.AR.Up.MI
