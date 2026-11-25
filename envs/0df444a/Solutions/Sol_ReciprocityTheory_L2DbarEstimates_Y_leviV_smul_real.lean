-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.leviV_smul_real
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:39:31.524131+00:00
-- url     : https://prove2.me/submissions/45660b64-186f-4a1a-9c9d-df5af9c366d0

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_AApproxD
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_AApproxE

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology Complex Metric
open scoped ContDiff ENNReal ComplexConjugate
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.Y
theorem _root_.solution {n : ℕ} (g : V n → ℂ) (u : V n) (r : ℝ) (ζ : V n) :
    leviV n g u (r • ζ).ofLp = ((r ^ 2 : ℝ) : ℂ) * leviV n g u ζ.ofLp := by
  unfold leviV
  simp only [WithLp.ofLp_smul, Pi.smul_apply, Complex.real_smul, map_mul, Complex.conj_ofReal,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  push_cast
  ring
end ReciprocityTheory.L2DbarEstimates.Y
