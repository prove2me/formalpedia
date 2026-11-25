-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.herm_eq_zero_of_trace_form_vanish
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:31:24.499052+00:00
-- url     : https://prove2.me/submissions/2f93a0f4-936f-4b4d-b537-dd2280046a24

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermitianTraceFormVanishing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermEqZeroOfTraceFormVanish
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_trace_form_integer_smul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_cc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_eq_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_intCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_natCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_neg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_add
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_cc
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_eq_zero
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_intCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_inv
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_mul
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_natCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_neg
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_one
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_sub
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_zero



set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open NumberField ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing
variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
namespace ReciprocityTheory.ChartRestriction.G.FD
theorem _root_.solution {r : ℕ} (ξ0 : E) (hξ0 : ξ0 ≠ 0) (G : Matrix (Fin r) (Fin r) E)
    (x y : Fin r → E) (h : ∀ β : 𝓞 E, EFf ξ0 G x (β • y) = 0) : herm G x y = 0 := by
  have hb : ∀ β : 𝓞 E, Algebra.trace ℚ E (cc (β : E) * (-ξ0 * herm G x y)) = 0 := fun β =>
    (trace_form_integer_smul ξ0 G x y β).symm.trans (h β)
  have hinv : ∀ a : E, cc (cc a) = a := by
    have h2 := pow_orderOf_eq_one (NumberField.IsCMField.complexConj E)
    rw [NumberField.IsCMField.orderOf_complexConj, pow_two] at h2
    intro a
    have := congrArg (fun σ => σ a) h2
    simpa [cc] using this
  have hw : ∀ w : E, Algebra.trace ℚ E (w * (-ξ0 * herm G x y)) = 0 := by
    intro w
    rw [← hinv w, ← (NumberField.integralBasis E).sum_repr (cc w)]
    simp only [cc, map_sum, map_rat_smul, Finset.sum_mul, smul_mul_assoc, LinearMap.map_smul]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [NumberField.integralBasis_apply]
    have := hb ((NumberField.RingOfIntegers.basis E) i)
    simp only [cc] at this
    rw [smul_eq_zero]
    exact Or.inr this
  have hz : -ξ0 * herm G x y = 0 := by
    have hnd := traceForm_nondegenerate ℚ E
    have hw' : ∀ w : E, Algebra.traceForm ℚ E (-ξ0 * herm G x y) w = 0 := fun w => by
      rw [Algebra.traceForm_apply, mul_comm]
      exact hw w
    first
      | exact hnd _ hw'
      | exact hnd.1 _ hw'
  rcases mul_eq_zero.1 hz with h1 | h1
  · exact absurd (neg_eq_zero.1 h1) hξ0
  · exact h1
end ReciprocityTheory.ChartRestriction.G.FD
