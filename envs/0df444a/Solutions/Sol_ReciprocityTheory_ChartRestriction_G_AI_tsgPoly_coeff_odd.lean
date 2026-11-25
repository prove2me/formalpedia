-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.tsgPoly_coeff_odd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:28:45.659837+00:00
-- url     : https://prove2.me/submissions/a1ca6042-e485-4c1e-9bae-aa9f8bd3afcb

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_APrime
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_TsgPolyVolPolyCoeffEven
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_tsgPoly_coeff_succ

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
theorem _root_.solution (D : ℕ) (κ : ℕ → ℝ) (P : ℝ[X]) (k : ℕ) :
    (tsgPoly D κ P).coeff (2 * k + 1) = 0 := by
  rw [tsgPoly_coeff_succ, if_neg (Nat.not_odd_iff_even.2 (even_two_mul k))]
end ReciprocityTheory.ChartRestriction.G.AI
