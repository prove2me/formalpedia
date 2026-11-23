-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.H1.JetApproximation.one_le_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:02:39.237285+00:00
-- url     : https://prove2.me/submissions/d5a1c22c-3fee-4e6a-853c-711354a28eaf

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_JetApproximation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.H1 ReciprocityTheory.ChartRestriction.G.H1.JetApproximation
variable {F R : Type*} [Field F] [CommRing R] [Algebra F R]
namespace ReciprocityTheory.ChartRestriction.G.H1.JetApproximation
theorem _root_.solution {V : Submodule F R} (h1 : 1 ≤ V) : ∀ n : ℕ, 1 ≤ V ^ n
  | 0 => by rw [pow_zero]
  | n + 1 => by
    rw [pow_succ]
    calc (1 : Submodule F R) = 1 * 1 := (mul_one 1).symm
      _ ≤ V ^ n * V := mul_le_mul' (solution h1 n) h1
end ReciprocityTheory.ChartRestriction.G.H1.JetApproximation
