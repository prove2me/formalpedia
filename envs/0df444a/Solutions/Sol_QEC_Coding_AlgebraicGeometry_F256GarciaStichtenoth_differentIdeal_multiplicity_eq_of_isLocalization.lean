-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.differentIdeal_multiplicity_eq_of_isLocalization
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:35:06.249691+00:00
-- url     : https://prove2.me/submissions/d8c14b89-25fc-4c50-a8f8-f9e0050d4f9d

import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.Localization.NormTrace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differents_Localization
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_multiplicity_map_eq_of_isLocalization
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_differentIdeal_map_eq_of_isLocalization

set_option autoImplicit false
open Module
open scoped nonZeroDivisors
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution
    (R S Rm Sm K L : Type*)
    [CommRing R] [CommRing S] [CommRing Rm] [CommRing Sm]
    [IsDomain R] [IsDomain S] [IsDomain Rm] [IsDomain Sm]
    [Field K] [Field L]
    [Algebra R S] [Algebra R Rm] [Algebra S Sm]
    [Algebra R Sm] [Algebra Rm Sm]
    [IsScalarTower R S Sm] [IsScalarTower R Rm Sm]
    [Algebra R K] [Algebra Rm K]
    [Algebra S L] [Algebra Sm L] [Algebra K L]
    [Algebra R L] [Algebra Rm L]
    [IsScalarTower R K L] [IsScalarTower Rm K L]
    [IsScalarTower R S L] [IsScalarTower Rm Sm L]
    [IsScalarTower S Sm L] [IsScalarTower R Sm L]
    [IsFractionRing R K] [IsFractionRing Rm K]
    [IsFractionRing S L] [IsFractionRing Sm L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Module.Free R S] [Module.Finite R S]
    [Module.IsTorsionFree R S] [Module.IsTorsionFree Rm Sm]
    [Module.IsTorsionFree S Sm]
    [IsIntegrallyClosed R] [IsIntegrallyClosed Rm]
    [IsIntegralClosure S R L] [IsIntegralClosure Sm Rm L]
    [IsDedekindDomain S] [IsDedekindDomain Sm]
    (M : Submonoid R)
    [IsLocalization M Rm]
    [IsLocalization (Algebra.algebraMapSubmonoid S M) Sm]
    [IsLocalization (Algebra.algebraMapSubmonoid S R⁰) L]
    [IsLocalization (Algebra.algebraMapSubmonoid Sm Rm⁰) L]
    (Q : Ideal S) [Q.IsMaximal]
    (hQ : Disjoint (Algebra.algebraMapSubmonoid S M : Set S) (Q : Set S)) :
    multiplicity (Ideal.map (algebraMap S Sm) Q) (differentIdeal Rm Sm) =
      multiplicity Q (differentIdeal R S) := by
  rw [← differentIdeal_map_eq_of_isLocalization R S Rm Sm K L M]
  exact multiplicity_map_eq_of_isLocalization S Sm
    (Algebra.algebraMapSubmonoid S M) Q (differentIdeal R S) hQ
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
