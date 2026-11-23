-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.FPw.paD_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:25:25.588803+00:00
-- url     : https://prove2.me/submissions/992b9f9c-6af5-4b13-9f3e-c72da8c2e2c0

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_FourierProjections_PaPolyTranslate
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_FourierProjections_PaIPZeroRight

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.I2.FPw
open MeasureTheory Complex
noncomputable section
variable {ι : Type} [Fintype ι]
open Classical
namespace ReciprocityTheory.ChartRestriction.G.I2.FPw
theorem _root_.solution (α : ι →₀ ℕ) {H1 H2 : EuclideanSpace ℂ ι → ℂ} (h1 : ContDiff ℂ (⊤ : ℕ∞) H1)
    (h2 : ContDiff ℂ (⊤ : ℕ∞) H2) : paD α (H1 + H2) = paD α H1 + paD α H2 := by
  unfold paD polyDeriv
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [iteratedFDeriv_add_apply (h1.contDiffAt.of_le (by exact_mod_cast le_top))
    (h2.contDiffAt.of_le (by exact_mod_cast le_top))]
  simp [mul_add]
end ReciprocityTheory.ChartRestriction.G.I2.FPw
