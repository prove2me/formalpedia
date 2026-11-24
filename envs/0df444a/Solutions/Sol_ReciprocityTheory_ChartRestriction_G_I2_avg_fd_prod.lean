-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.avg_fd_prod
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:14:02.010187+00:00
-- url     : https://prove2.me/submissions/4c1d1691-8966-4f93-b63b-9da0b612e5aa

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PolyDerivMonomialOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GaussianTailBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_LemmaS
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_RCauchy
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_L2NormFundamentalDomain

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open MeasureTheory Complex
noncomputable section
variable {E : Type} [Field E] [NumberField E] (X : PT E)
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution {n : ℕ} (f : Fin n → Vsp X.dim → ℝ) :
    ⨍ v in X.fd n, ∏ k, f k (v k) = ∏ k, ⨍ x in ZSpan.fundamentalDomain X.b, f k x := by
  have hfd : X.fd n = Set.univ.pi (fun _ : Fin n => ZSpan.fundamentalDomain X.b) := by
    ext v; simp [PT.fd]
  rw [hfd]
  simp only [MeasureTheory.setAverage_eq, smul_eq_mul]
  rw [MeasureTheory.volume_pi, MeasureTheory.Measure.restrict_pi_pi]
  simp only [MeasureTheory.measureReal_def]
  rw [MeasureTheory.Measure.pi_pi, ENNReal.toReal_prod, ← Finset.prod_inv_distrib]
  first
  | rw [MeasureTheory.integral_fintype_prod_eq_prod, ← Finset.prod_mul_distrib]
  | rw [MeasureTheory.integral_fintype_prod_eq_prod (μ := fun _ => _), ← Finset.prod_mul_distrib]
end ReciprocityTheory.ChartRestriction.G.I2
