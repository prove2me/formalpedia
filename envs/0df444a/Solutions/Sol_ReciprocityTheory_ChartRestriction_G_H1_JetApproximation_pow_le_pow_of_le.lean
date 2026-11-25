-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.H1.JetApproximation.pow_le_pow_of_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:07:53.304088+00:00
-- url     : https://prove2.me/submissions/ad9e27bc-7627-4f75-8e74-023084d63f89

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
theorem _root_.solution {V W : Submodule F R} (h : V ≤ W) : ∀ n : ℕ, V ^ n ≤ W ^ n
  | 0 => le_rfl
  | n + 1 => by
    rw [pow_succ, pow_succ]
    exact mul_le_mul' (solution h n) h
end ReciprocityTheory.ChartRestriction.G.H1.JetApproximation
