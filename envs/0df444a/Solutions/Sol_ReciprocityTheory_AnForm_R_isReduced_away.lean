-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.isReduced_away
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:17:25.794999+00:00
-- url     : https://prove2.me/submissions/1561e430-e85b-4eb8-9174-15032346c74a

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjDehom
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_LogResStC
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_FinTypeQE
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjHypA

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
namespace ReciprocityTheory.AnForm.R
theorem _root_.solution {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hP : IsMultiHomogIdeal P)
    (hrad : P.IsRadical) (p : (k : K) → ι k) :
    letI := segreGraded hP
    _root_.IsReduced (HomogeneousLocalization.Away (segreGrading P) (segreW P p)) := by
  letI := segreGraded hP
  have : _root_.IsReduced (MvPolynomial ((k : K) → ι k) ℂ ⧸ segreIdeal P) :=
    (Ideal.isRadical_iff_quotient_reduced _).mp (hrad.comap _)
  exact isReduced_of_injective (algebraMap _ (Localization.Away (segreW P p)))
    (HomogeneousLocalization.val_injective _)
end ReciprocityTheory.AnForm.R
