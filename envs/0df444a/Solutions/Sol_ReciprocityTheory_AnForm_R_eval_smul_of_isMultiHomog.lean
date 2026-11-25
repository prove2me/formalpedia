-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.eval_smul_of_isMultiHomog
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:08:31.496115+00:00
-- url     : https://prove2.me/submissions/f719f5cb-7025-4737-a249-0dc07fcc9004

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IsOpenAlt
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_MemConePtsIffChartIdeal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open MvPolynomial
noncomputable section
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace ReciprocityTheory.AnForm.R
theorem _root_.solution {f : MvPolynomial (Σ k, ι k) ℂ} {a : K → ℕ}
    (hf : IsMultiHomog f a) (c : K → ℂ) (y : (Σ k, ι k) → ℂ) :
    eval (fun q => c q.1 * y q) f = (∏ k, c k ^ a k) * eval y f := by
  rw [MvPolynomial.eval_eq', MvPolynomial.eval_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl (fun d hd => ?_)
  have hc : ∏ q : (Σ k, ι k), c q.1 ^ d q = ∏ k, c k ^ a k := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl (fun k _ => ?_)
    dsimp only
    rw [Finset.prod_pow_eq_pow_sum, hf d hd k]
  have key : ∏ q, (c q.1 * y q) ^ d q = (∏ k, c k ^ a k) * ∏ q, y q ^ d q := by
    rw [← hc, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl (fun q _ => mul_pow _ _ _)
  linear_combination (coeff d f) * key
end ReciprocityTheory.AnForm.R
