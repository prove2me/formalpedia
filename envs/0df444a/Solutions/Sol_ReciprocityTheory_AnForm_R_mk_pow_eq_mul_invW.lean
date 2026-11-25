-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.mk_pow_eq_mul_invW
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:08:32.69886+00:00
-- url     : https://prove2.me/submissions/0d764768-29ae-4eee-a42e-ed3d48621abe

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
theorem _root_.solution (P : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (p : (k : K) → ι k)
    (a : MvPolynomial ((k : K) → ι k) ℂ ⧸ segreIdeal P) (n : ℕ) (h : segreW P p ^ n ∈ Submonoid.powers (segreW P p)) :
    (Localization.mk a ⟨segreW P p ^ n, h⟩ : Localization.Away (segreW P p)) =
      Localization.mk a 1 * invW P p ^ n := by
  rw [invW, Localization.mk_pow, Localization.mk_mul, one_pow, mul_one, one_mul]
  congr 1
end ReciprocityTheory.AnForm.R
