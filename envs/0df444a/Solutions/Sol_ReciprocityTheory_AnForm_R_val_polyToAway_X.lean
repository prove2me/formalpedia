-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.val_polyToAway_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:24:57.661844+00:00
-- url     : https://prove2.me/submissions/173a3286-529e-414a-82fe-231f9b376ce7

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjHypA
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjHypC

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open MvPolynomial AlgebraicGeometry CategoryTheory
noncomputable section
variable {K : Type} [Fintype K] [Nonempty K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hP : IsMultiHomogIdeal P) (p : (k : K) → ι k)
namespace ReciprocityTheory.AnForm.R
theorem _root_.solution (q : Σ k, ι k) :
    letI := segreGraded hP
    (polyToAway hP p (X q)).val = IsLocalization.mk' (Localization.Away (segreW P p))
      (segreW P (chartUpd p q)) (⟨segreW P p, Submonoid.mem_powers _⟩ : Submonoid.powers (segreW P p)) := by
  simp only [polyToAway, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X]
  unfold awayCoord
  rw [HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk']
  congr 1
  exact Subtype.ext (pow_one _)
end ReciprocityTheory.AnForm.R
