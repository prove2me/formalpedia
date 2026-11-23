-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.H1.JetApproximation.pow_le_ideal_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:03:26.080171+00:00
-- url     : https://prove2.me/submissions/db310015-2efd-4bf0-b751-890af57ddedb

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
theorem _root_.solution {W : Submodule F R} {m : Ideal R} (h : W ≤ m.restrictScalars F) :
    ∀ k : ℕ, W ^ k ≤ (m ^ k).restrictScalars F
  | 0 => by
    intro x _
    simp [Ideal.one_eq_top]
  | k + 1 => by
    rw [pow_succ]
    refine Submodule.mul_le.2 fun a ha b hb => ?_
    rw [Submodule.restrictScalars_mem, pow_succ]
    exact Ideal.mul_mem_mul (solution h k ha) (h hb)
end ReciprocityTheory.ChartRestriction.G.H1.JetApproximation
