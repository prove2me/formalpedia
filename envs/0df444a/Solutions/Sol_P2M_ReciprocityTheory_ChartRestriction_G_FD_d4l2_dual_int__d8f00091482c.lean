-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_G_FD_d4l2_dual_int__d8f00091482c
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:56:50.045283+00:00
-- url     : https://prove2.me/submissions/ced76aa7-d118-40d7-b469-80cb9d86488e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsotropicOutsideLine
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ConjugateConjugate
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_d4l2_dual_int

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex Module
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace ReciprocityTheory.ChartRestriction.G.FD
theorem _root_.solution (t : E) (h : ∀ γ : 𝓞 E, ∃ k : ℤ, Algebra.trace ℚ E (t * γ) = k) :
    IsIntegral ℤ (((NumberField.discr E).natAbs : E) * t) := by
  have key := d4l2_dual_int t h
  rcases Int.natAbs_eq (NumberField.discr E) with hd | hd
  · have e : ((NumberField.discr E).natAbs : E) = (NumberField.discr E : E) := by
      conv_rhs => rw [hd]
      simp
    rw [e]
    exact key
  · have e : ((NumberField.discr E).natAbs : E) = -(NumberField.discr E : E) := by
      conv_rhs => rw [hd]
      simp
    rw [e, neg_mul]
    exact key.neg
end ReciprocityTheory.ChartRestriction.G.FD
