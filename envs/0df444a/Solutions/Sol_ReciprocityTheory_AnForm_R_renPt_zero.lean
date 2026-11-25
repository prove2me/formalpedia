-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.renPt_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:16:11.532601+00:00
-- url     : https://prove2.me/submissions/05b10411-a6c4-45c3-9f1d-d47070f23496

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjHyp
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_JacChart
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_LocTransfer
import Theorems.Thm_ReciprocityTheory_AnForm_R_mem_map_renR_iff

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
noncomputable section
variable {σ : Type} [Fintype σ]
namespace ReciprocityTheory.AnForm.R
theorem _root_.solution (I : Ideal (MvPolynomial σ ℂ)) (z : σ → ℂ) (hz : ∀ h ∈ I, eval z h = 0) :
    ∀ h ∈ I.map (renR σ : MvPolynomial σ ℂ →+* _), eval (renPt z) h = 0 := by
  intro h hh
  rw [mem_map_renR_iff] at hh
  have e := eval_renC z ((renR σ).symm h)
  rw [show renC σ ((renR σ).symm h) = h from (renR σ).apply_symm_apply h] at e
  rw [e]
  exact hz _ hh
end ReciprocityTheory.AnForm.R
