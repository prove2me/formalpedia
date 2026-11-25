-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.sum_blockWt_eval
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:13:47.968113+00:00
-- url     : https://prove2.me/submissions/5bc37d6e-367d-407c-9675-97bb31e0e91c

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjHyp
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ConeChartA
import Theorems.Thm_ReciprocityTheory_AnForm_R_isWeightedHomogeneous_blockWt

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
theorem _root_.solution {f : MvPolynomial (Σ k, ι k) ℂ} {dg : K → ℕ} (hf : IsMultiHomog f dg)
    (k : K) (z : (Σ k, ι k) → ℂ) :
    ∑ q, (blockWt k q : ℂ) * (z q * eval z (pderiv q f)) = (dg k : ℂ) * eval z f := by
  have h := congrArg (eval z) (isWeightedHomogeneous_blockWt hf k).sum_weight_X_mul_pderiv
  simpa [map_sum, nsmul_eq_mul] using h
end ReciprocityTheory.AnForm.R
