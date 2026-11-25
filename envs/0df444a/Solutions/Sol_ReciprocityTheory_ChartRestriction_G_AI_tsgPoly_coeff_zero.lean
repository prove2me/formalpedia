-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.tsgPoly_coeff_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:28:48.224737+00:00
-- url     : https://prove2.me/submissions/57d2b64e-050a-4a7b-bab5-0e85b39076d4

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_APrime
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_TsgPolyVolPolyCoeffEven

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AI
open Polynomial
namespace ReciprocityTheory.ChartRestriction.G.AI
theorem _root_.solution (D : ℕ) (κ : ℕ → ℝ) (P : ℝ[X]) : (tsgPoly D κ P).coeff 0 = 0 := by
  rw [tsgPoly, Polynomial.finset_sum_coeff]
  refine Finset.sum_eq_zero fun n _ => ?_
  split_ifs <;> simp [Polynomial.coeff_C_mul_X_pow]
end ReciprocityTheory.ChartRestriction.G.AI
