-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.Data.re_sum_Psi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:59:23.307455+00:00
-- url     : https://prove2.me/submissions/f0b3972a-9bca-44af-ac0e-c2b6945f3cfd

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsotropicOutsideLine
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ConjugateConjugate
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_trace_eq_Psi

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
open ReciprocityTheory.ChartRestriction.G.FD.Data
variable {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.Data
theorem _root_.solution (y : E) : (∑ τ : X.Ψ, τ.1 y).re = (Algebra.trace ℚ E y : ℝ) / 2 := by
  have h := congrArg Complex.re (X.trace_eq_Psi y)
  simp only [Complex.ratCast_re, Complex.re_sum, Complex.add_re, Complex.conj_re] at h
  rw [Complex.re_sum, h, Finset.sum_add_distrib]
  ring
end ReciprocityTheory.ChartRestriction.G.FD.Data
