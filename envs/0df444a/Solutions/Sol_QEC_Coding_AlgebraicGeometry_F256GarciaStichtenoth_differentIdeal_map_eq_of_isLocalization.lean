-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.differentIdeal_map_eq_of_isLocalization
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:33:47.505365+00:00
-- url     : https://prove2.me/submissions/0d5f7ce6-0e36-4c1d-88da-2d53202924c7

import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.Localization.NormTrace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differents_Localization
section
open Module
open scoped nonZeroDivisors
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
private theorem traceDual_one_span_eq_of_isLocalization
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
    (M : Submonoid R)
    [IsLocalization M Rm]
    [IsLocalization (Algebra.algebraMapSubmonoid S M) Sm]
    [IsLocalization (Algebra.algebraMapSubmonoid S R⁰) L]
    [IsLocalization (Algebra.algebraMapSubmonoid Sm Rm⁰) L] :
    Submodule.span Sm
        (Submodule.traceDual R K (1 : Submodule S L) : Set L) =
      Submodule.traceDual Rm K (1 : Submodule Sm L) := by
  classical
  let b := Module.Free.chooseBasis R S
  let bK := b.localizationLocalization K R⁰ L
  let bm := b.localizationLocalization Rm M Sm
  let bmK := bm.localizationLocalization K Rm⁰ L
  letI : Finite (Module.Free.ChooseBasisIndex R S) :=
    Module.Finite.finite_basis b
  have hbK : bmK = bK := by
    apply DFunLike.coe_injective
    funext i
    simp only [bmK, bm, bK, Basis.localizationLocalization_apply]
    rw [IsScalarTower.algebraMap_apply S Sm L]
  have hb :
      (1 : Submodule S L).restrictScalars R =
        Submodule.span R (Set.range bK) := by
    rw [b.localizationLocalization_span K R⁰ L]
    ext x
    simp only [Submodule.restrictScalars_mem, Submodule.mem_one,
      LinearMap.mem_range]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y, rfl⟩
    · rintro ⟨y, rfl⟩
      exact ⟨y, rfl⟩
  have hbm :
      (1 : Submodule Sm L).restrictScalars Rm =
        Submodule.span Rm (Set.range bmK) := by
    rw [bm.localizationLocalization_span K Rm⁰ L]
    ext x
    simp only [Submodule.restrictScalars_mem, Submodule.mem_one,
      LinearMap.mem_range]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y, rfl⟩
    · rintro ⟨y, rfl⟩
      exact ⟨y, rfl⟩
  have hdual := Submodule.traceDual_span_of_basis R
    (1 : Submodule S L) bK hb
  have hdual_m := Submodule.traceDual_span_of_basis Rm
    (1 : Submodule Sm L) bmK hbm
  rw [show (Submodule.traceDual R K (1 : Submodule S L) : Set L) =
      ((Submodule.traceDual R K (1 : Submodule S L)).restrictScalars R : Set L) by
        rfl,
    hdual, Submodule.span_span_of_tower, ← hbK,
    ← Submodule.span_span_of_tower (R := Rm) (S := Sm), ← hdual_m]
  exact Submodule.span_eq _
private theorem dual_one_extendedHom_eq_of_isLocalization
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
    [Module.IsTorsionFree S Sm]
    [IsIntegrallyClosed R] [IsIntegrallyClosed Rm]
    [IsIntegralClosure S R L] [IsIntegralClosure Sm Rm L]
    [IsDedekindDomain S] [IsDedekindDomain Sm]
    (M : Submonoid R)
    [IsLocalization M Rm]
    [IsLocalization (Algebra.algebraMapSubmonoid S M) Sm]
    [IsLocalization (Algebra.algebraMapSubmonoid S R⁰) L]
    [IsLocalization (Algebra.algebraMapSubmonoid Sm Rm⁰) L] :
    (FractionalIdeal.dual R K (1 : FractionalIdeal S⁰ L)).extendedHom L Sm =
      FractionalIdeal.dual Rm K (1 : FractionalIdeal Sm⁰ L) := by
  classical
  let hf : S⁰ ≤ Submonoid.comap (algebraMap S Sm) Sm⁰ :=
    nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
      (FaithfulSMul.algebraMap_injective S Sm)
  have hmap :
      IsLocalization.map L (algebraMap S Sm) hf = RingHom.id L := by
    apply IsLocalization.ringHom_ext S⁰
    ext x
    simp only [RingHom.comp_apply, RingHom.id_apply]
    rw [IsLocalization.map_eq]
    exact (IsScalarTower.algebraMap_apply S Sm L x).symm
  have hdual_set :
      (FractionalIdeal.dual R K (1 : FractionalIdeal S⁰ L) : Set L) =
        (Submodule.traceDual R K (1 : Submodule S L) : Set L) := by
    change
      ((FractionalIdeal.dual R K (1 : FractionalIdeal S⁰ L) :
          Submodule S L) : Set L) = _
    rw [FractionalIdeal.coe_dual_one]
  apply FractionalIdeal.coeToSubmodule_injective
  change
    (FractionalIdeal.extended L hf
        (FractionalIdeal.dual R K (1 : FractionalIdeal S⁰ L)) :
      Submodule Sm L) =
      (FractionalIdeal.dual Rm K (1 : FractionalIdeal Sm⁰ L) :
        Submodule Sm L)
  rw [FractionalIdeal.coe_extended_eq_span, hmap, hdual_set,
    FractionalIdeal.coe_dual_one]
  simpa only [RingHom.id_apply, Set.image_id'] using
    traceDual_one_span_eq_of_isLocalization R S Rm Sm K L M
end
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
end

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
    [IsLocalization (Algebra.algebraMapSubmonoid Sm Rm⁰) L] :
    Ideal.map (algebraMap S Sm) (differentIdeal R S) =
      differentIdeal Rm Sm := by
  rw [← FractionalIdeal.coeIdeal_inj (K := L),
    ← FractionalIdeal.extendedHom_coeIdeal_eq_map (K := L) L Sm,
    coeIdeal_differentIdeal R K L S,
    coeIdeal_differentIdeal Rm K L Sm, map_inv₀,
    dual_one_extendedHom_eq_of_isLocalization R S Rm Sm K L M]
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
