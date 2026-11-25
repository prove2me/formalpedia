-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.MHF.coeff_psiB_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:43:23.201725+00:00
-- url     : https://prove2.me/submissions/ce1306e1-6346-4ce3-a56a-f8daa663f887

import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereLogIntegrableStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_CoeffPsiBNeZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_MHF_psiB_monomial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0 ReciprocityTheory.ChartRestriction.G.T0.MHF
open MvPolynomial ReciprocityTheory.MultiplicativeHeights
variable {K : Type*} [Field K] {B n : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.T0.MHF
theorem _root_.solution (b : Fin B) (f : MvPolynomial (Fin B × Fin n) K)
    (s : Fin B × Fin n →₀ ℕ) (hs : s ∈ f.support) : (psiB b f).coeff (bw b s) ≠ 0 := by
  classical
  intro h0
  have h1 := congrArg (MvPolynomial.coeff s) h0
  conv at h1 => lhs; rw [f.as_sum]
  rw [map_sum, Polynomial.finsetSum_coeff, coeff_sum] at h1
  simp only [psiB_monomial, Polynomial.coeff_C_mul_X_pow, coeff_zero] at h1
  rw [Finset.sum_eq_single s] at h1
  · simp at h1; exact (mem_support_iff.1 hs) h1
  · intro s' _ hne
    split_ifs <;> simp [coeff_monomial, hne]
  · intro h; exact absurd hs h
end ReciprocityTheory.ChartRestriction.G.T0.MHF
