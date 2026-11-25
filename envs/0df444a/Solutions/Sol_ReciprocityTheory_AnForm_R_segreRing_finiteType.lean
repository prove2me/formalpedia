-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.segreRing_finiteType
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:31:09.257181+00:00
-- url     : https://prove2.me/submissions/fea85149-ca3e-41c2-affe-b03347f21a08

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
variable [Nonempty K]
namespace ReciprocityTheory.AnForm.R
theorem _root_.solution {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hP : IsMultiHomogIdeal P) :
    letI := segreGraded hP
    Algebra.FiniteType (segreGrading P 0) (MvPolynomial ((k : K) → ι k) ℂ ⧸ segreIdeal P) := by
  letI := segreGraded hP
  haveI : Algebra.FiniteType ℂ (MvPolynomial ((k : K) → ι k) ℂ ⧸ segreIdeal P) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℂ (segreIdeal P))
      (Ideal.Quotient.mkₐ_surjective ℂ _)
  haveI : IsScalarTower ℂ (segreGrading P 0) (MvPolynomial ((k : K) → ι k) ℂ ⧸ segreIdeal P) :=
    IsScalarTower.of_algebraMap_eq fun c => by
      rw [← SetLike.GradeZero.coe_algebraMap (segreGrading P) c]
      rfl
  exact Algebra.FiniteType.of_restrictScalars_finiteType ℂ (segreGrading P 0) _
end ReciprocityTheory.AnForm.R
