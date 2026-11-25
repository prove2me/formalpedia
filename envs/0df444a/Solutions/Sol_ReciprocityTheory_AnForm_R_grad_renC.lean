-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.grad_renC
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:12:21.138715+00:00
-- url     : https://prove2.me/submissions/93ca6cc4-302a-498f-9a0d-d48c638f9b92

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjHyp
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_LocTransfer
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ConeChartB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open MvPolynomial IsLocalRing
namespace ReciprocityTheory.AnForm.R
theorem _root_.solution {σ : Type} [Fintype σ] (z : σ → ℂ) (h : MvPolynomial σ ℂ) :
    grad (renPt z) (renC σ h) = fun j => eval z (pderiv ((Fintype.equivFin σ).symm j) h) := by
  funext j
  simp only [grad, renC, renameEquiv_apply]
  conv_lhs => rw [← Equiv.apply_symm_apply (Fintype.equivFin σ) j]
  rw [pderiv_rename (Equiv.injective _), eval_rename]
  have hc : renPt z ∘ (Fintype.equivFin σ) = z := by
    funext i
    simp [renPt]
  rw [hc]
end ReciprocityTheory.AnForm.R
