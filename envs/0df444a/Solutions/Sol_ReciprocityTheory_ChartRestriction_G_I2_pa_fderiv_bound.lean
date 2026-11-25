-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.pa_fderiv_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:29:12.959723+00:00
-- url     : https://prove2.me/submissions/54614c10-96bd-4947-8a05-5720335e991e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PropAB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_RCauchy
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PropAC
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_pa_cauchy1

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open MeasureTheory Complex Metric
noncomputable section
variable {ι : Type} [Fintype ι]
open Classical
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution {κ : Type} (G : κ → EuclideanSpace ℂ ι → ℂ) (hG : ∀ k, Differentiable ℂ (G k))
    (R : ℝ) (u : κ → ℝ) (hu : ∀ k v, ‖v‖ ≤ R + 1 → ‖G k v‖ ≤ u k) (j : ι) :
    ∀ k y, ‖y‖ ≤ R → ‖fderiv ℂ (G k) y (EuclideanSpace.single j 1)‖ ≤ u k := by
  intro k y hy
  refine pa_cauchy1 (hG k) y j fun t ht => hu k _ ?_
  calc ‖y + t • EuclideanSpace.single j (1 : ℂ)‖ ≤ ‖y‖ + ‖t • EuclideanSpace.single j (1 : ℂ)‖ := norm_add_le _ _
    _ = ‖y‖ + 1 := by rw [norm_smul, EuclideanSpace.norm_single, ht, norm_one, mul_one]
    _ ≤ R + 1 := by linarith
end ReciprocityTheory.ChartRestriction.G.I2
