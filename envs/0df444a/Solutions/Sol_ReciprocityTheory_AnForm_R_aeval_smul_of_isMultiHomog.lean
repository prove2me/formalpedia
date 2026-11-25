-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.aeval_smul_of_isMultiHomog
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:03:07.814795+00:00
-- url     : https://prove2.me/submissions/11958078-dcb1-4e29-8311-30fbf387f61d

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjHyp
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ConeChartA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open MvPolynomial Algebra
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace ReciprocityTheory.AnForm.R
theorem _root_.solution {T : Type*} [CommRing T] [Algebra ℂ T]
    {f : MvPolynomial (Σ k, ι k) ℂ} {a : K → ℕ}
    (hf : IsMultiHomog f a) (c : K → T) (y : (Σ k, ι k) → T) :
    aeval (fun q => c q.1 * y q) f = (∏ k, c k ^ a k) * aeval y f := by
  classical
  conv_lhs => rw [f.as_sum]
  conv_rhs => rw [f.as_sum]
  simp only [map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [aeval_monomial, aeval_monomial, Finsupp.prod_pow, Finsupp.prod_pow]
  have e : ∏ q : (Σ k, ι k), (c q.1 * y q) ^ m q = (∏ k, c k ^ a k) * ∏ q, y q ^ m q := by
    simp_rw [mul_pow]
    rw [Finset.prod_mul_distrib, Fintype.prod_sigma]
    congr 1
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ i, c k ^ m ⟨k, i⟩ = c k ^ a k
    rw [Finset.prod_pow_eq_pow_sum, hf m hm k]
  rw [e]
  ring
end ReciprocityTheory.AnForm.R
