-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.lemS_finrank
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:09:38.182747+00:00
-- url     : https://prove2.me/submissions/e6444a62-a71f-415b-a8c1-f65ec8251afd

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_RSubMean
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_LemmaSB

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
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution : Module.finrank ℝ (EuclideanSpace ℂ ι) = 2 * Fintype.card ι := by
  first
  | rw [← Module.finrank_mul_finrank ℝ ℂ (EuclideanSpace ℂ ι), Complex.finrank_real_complex,
      finrank_euclideanSpace]
  | rw [← FiniteDimensional.finrank_mul_finrank ℝ ℂ (EuclideanSpace ℂ ι),
      Complex.finrank_real_complex, finrank_euclideanSpace]
  | (rw [(WithLp.linearEquiv 2 ℝ (ι → ℂ)).finrank_eq, Module.finrank_pi_fintype]
     simp [Complex.finrank_real_complex, mul_comm])
  | simp [← Module.finrank_mul_finrank ℝ ℂ (EuclideanSpace ℂ ι), Complex.finrank_real_complex,
      finrank_euclideanSpace]
end ReciprocityTheory.ChartRestriction.G.I2
