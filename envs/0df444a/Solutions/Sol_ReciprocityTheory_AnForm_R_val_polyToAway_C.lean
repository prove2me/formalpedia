-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.val_polyToAway_C
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:14:54.325321+00:00
-- url     : https://prove2.me/submissions/6e9dca6d-8b54-4b8a-b751-cb75b7db26fe

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
theorem _root_.solution (c : ℂ) :
    letI := segreGraded hP
    (polyToAway hP p (C c)).val =
      algebraMap _ (Localization.Away (segreW P p)) (Ideal.Quotient.mk (segreIdeal P) (C c)) := by
  simp only [polyToAway, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C, RingHom.comp_apply]
  rw [← Localization.mk_one_eq_algebraMap]
  first
  | rfl
  | (rw [← HomogeneousLocalization.algebraMap_apply]; rfl)
  | simp [HomogeneousLocalization.val_fromZeroRingHom, Localization.mk_one_eq_algebraMap,
      SetLike.GradeZero.coe_algebraMap, Ideal.Quotient.algebraMap_eq, MvPolynomial.algebraMap_eq]
end ReciprocityTheory.AnForm.R
