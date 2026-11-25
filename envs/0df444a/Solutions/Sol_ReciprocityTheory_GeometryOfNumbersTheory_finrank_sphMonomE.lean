-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.finrank_sphMonomE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:01:30.469368+00:00
-- url     : https://prove2.me/submissions/c1225ab5-2362-4e01-81ea-3fff8cfbffd7

import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_SphericalMonomials_GaussSt
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_SphericalMonomials_MonomStA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.GeometryOfNumbersTheory
open MeasureTheory Metric Set
variable (N : ℕ)
namespace ReciprocityTheory.GeometryOfNumbersTheory
theorem _root_.solution : Module.finrank ℝ (EuclideanSpace ℂ (Fin N)) = 2 * N := by
  rw [← Module.finrank_mul_finrank ℝ ℂ, Complex.finrank_real_complex, finrank_euclideanSpace,
    Fintype.card_fin]
end ReciprocityTheory.GeometryOfNumbersTheory
