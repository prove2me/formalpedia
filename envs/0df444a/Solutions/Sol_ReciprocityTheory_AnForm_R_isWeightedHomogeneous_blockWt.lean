-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.isWeightedHomogeneous_blockWt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:47:33.206768+00:00
-- url     : https://prove2.me/submissions/e1c0c383-af52-4003-ba44-9c824382c49f

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
theorem _root_.solution {f : MvPolynomial (Σ k, ι k) ℂ} {dg : K → ℕ}
    (hf : IsMultiHomog f dg) (k : K) : IsWeightedHomogeneous (blockWt k) f (dg k) := by
  intro d hd
  have hs : d ∈ f.support := MvPolynomial.mem_support_iff.mpr hd
  rw [← hf d hs k]
  simp only [Finsupp.weight_apply, smul_eq_mul]
  rw [Finsupp.sum_fintype _ _ (by simp)]
  rw [Fintype.sum_sigma, Fintype.sum_eq_single k]
  · simp [blockWt]
  · intro k' hk'
    simp [blockWt, hk']
end ReciprocityTheory.AnForm.R
