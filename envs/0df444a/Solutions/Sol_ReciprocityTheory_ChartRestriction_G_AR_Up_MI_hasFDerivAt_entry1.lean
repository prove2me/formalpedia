-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.MI.hasFDerivAt_entry1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:33:41.471781+00:00
-- url     : https://prove2.me/submissions/2e6184ce-f501-4a5d-b0af-a736049d76ce

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
theorem _root_.solution (w : Ix ι r → ℂ) (τ : ι) (a k : Fin r) :
    HasFDerivAt (fun v : Ix ι r → ℂ => (1 + sl v τ) a k)
      (if k < a then ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Ix ι r => ℂ) (τ, a, k) else 0) w := by
  by_cases hk : k < a
  · rw [if_pos hk]
    have hf : (fun v : Ix ι r → ℂ => (1 + sl v τ) a k) =
        fun v => (1 : Matrix (Fin r) (Fin r) ℂ) a k + v (τ, a, k) := by
      funext v
      simp [sl, hk]
    rw [hf]
    exact (hasFDerivAt_apply (𝕜 := ℝ) (τ, a, k) w).const_add _
  · rw [if_neg hk]
    have hf : (fun v : Ix ι r → ℂ => (1 + sl v τ) a k) =
        fun _ => (1 : Matrix (Fin r) (Fin r) ℂ) a k := by
      funext v
      simp [sl, hk]
    rw [hf]
    exact hasFDerivAt_const _ _
end ReciprocityTheory.ChartRestriction.G.AR.Up.MI
