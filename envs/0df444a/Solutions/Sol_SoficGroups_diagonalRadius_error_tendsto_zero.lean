-- Prove2me | solution 1 for SoficGroups.diagonalRadius_error_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:51.68578+00:00
-- url     : https://prove2.me/submissions/b6f3243e-669e-4b1f-86bd-496a658e929b

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_diagonalRadius_tendsto_atTop
import Theorems.Thm_SoficGroups_diagonalRadius_eventually_error_lt

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
namespace SoficGroups
theorem _root_.solution (e : ℕ → ℕ → ℝ)
    (hnonneg : ∀ n k, 0 ≤ e n k)
    (he : ∀ k, Tendsto (fun n => e n k) atTop (𝓝 0)) :
    Tendsto (fun n => e n (diagonalRadius e n)) atTop (𝓝 0) := by
  have hbound : ∀ᶠ n in atTop,
      e n (diagonalRadius e n) ≤
        1 / ((diagonalRadius e n : ℝ) + 1) :=
    (diagonalRadius_eventually_error_lt e he).mono fun _ h => h.le
  have hlimit : Tendsto
      (fun n => 1 / ((diagonalRadius e n : ℝ) + 1)) atTop (𝓝 0) := by
    simpa only [Function.comp_def] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
        (diagonalRadius_tendsto_atTop e he)
  exact squeeze_zero'
    (Eventually.of_forall fun n => hnonneg n (diagonalRadius e n))
    hbound hlimit
end SoficGroups
