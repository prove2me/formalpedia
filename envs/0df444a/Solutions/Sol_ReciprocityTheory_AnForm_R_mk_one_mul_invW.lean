-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.mk_one_mul_invW
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:08:31.37585+00:00
-- url     : https://prove2.me/submissions/c9041c99-5219-4c02-91ad-9b34107b35dd

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_SegreIdealIsHomogeneous
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjDehomA

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
theorem _root_.solution (P : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (p : (k : K) → ι k) :
    Localization.mk (segreW P p) 1 * invW P p = 1 := by
  rw [invW, Localization.mk_mul, mul_one, one_mul]
  exact Localization.mk_self (⟨segreW P p, 1, pow_one _⟩ : Submonoid.powers (segreW P p))
end ReciprocityTheory.AnForm.R
