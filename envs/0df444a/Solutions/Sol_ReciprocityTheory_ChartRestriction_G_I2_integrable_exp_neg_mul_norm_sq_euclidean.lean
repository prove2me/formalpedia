-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.integrable_exp_neg_mul_norm_sq_euclidean
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:10:30.27461+00:00
-- url     : https://prove2.me/submissions/9d436f9b-9994-4711-b7be-3d63ccd82a31

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_IntegrableNormPowMulExpNegMulNormSq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open MeasureTheory
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution {g : ℕ} {b : ℝ} (hb : 0 < b) :
    Integrable (fun z : EuclideanSpace ℂ (Fin g) => Real.exp (-b * ‖z‖ ^ 2)) := by
  have hc := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := EuclideanSpace ℂ (Fin g))
    (b := (b : ℂ)) (by simpa using hb) 0 0
  refine hc.norm.congr (Filter.Eventually.of_forall fun z => ?_)
  simp only [zero_mul, add_zero]
  rw [Complex.norm_exp]
  congr 1
  simp [← Complex.ofReal_pow]
end ReciprocityTheory.ChartRestriction.G.I2
