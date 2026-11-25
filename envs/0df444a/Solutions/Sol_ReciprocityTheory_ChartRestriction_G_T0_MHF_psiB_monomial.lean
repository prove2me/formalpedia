-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.MHF.psiB_monomial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:36:42.206453+00:00
-- url     : https://prove2.me/submissions/cbbc03fd-c2be-4fe3-993e-8859e734082a

import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereLogIntegrableStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_CoeffPsiBNeZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_MHF_bw_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_MHF_bw_single
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_MHF_psiB_X

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
theorem _root_.solution (b : Fin B) (s : Fin B × Fin n →₀ ℕ) (a : K) :
    psiB b (monomial s a) = Polynomial.C (monomial s a) * Polynomial.X ^ bw b s := by
  induction s using Finsupp.induction generalizing a
  · simp [psiB, bw, MvPolynomial.algebraMap_eq, Polynomial.algebraMap_apply]
  · rename_i v e f _ _ ih
    rw [monomial_single_add, map_mul, map_pow, ih, psiB_X, bw_add, bw_single]
    split_ifs <;> simp only [map_mul, map_pow, mul_pow, ← pow_mul, pow_add, mul_one, mul_zero,
      pow_zero, add_zero, zero_add] <;> ring
end ReciprocityTheory.ChartRestriction.G.T0.MHF
