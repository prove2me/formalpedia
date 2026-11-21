-- Prove2me | solution 1 for RiemannMasullo.picMapAlgebra_surjective_of_isLocalization
-- status  : ACCEPTED   (prove)
-- author  : @koffie
-- created : 2026-11-20T23:07:44.663461+00:00
-- url     : https://prove2.me/submissions/18b46f43-2ba7-4ec1-b7f0-2b34915ab301

-- Adapted from mccorvie/riemann-masullo, Apache-2.0.
-- https://github.com/mccorvie/riemann-masullo/blob/9d5c8b94a1f1b5d8f903f1b04d1e043877e7bb15/RiemannMasullo/ForMathlib/RingTheory/PicardGroup.lean
import Mathlib

open CommRing IsDedekindDomain
open scoped nonZeroDivisors

variable {R : Type*} [CommRing R] [IsDedekindDomain R]

/-- The Picard class of a nonzero integral ideal is represented by that ideal as a module. -/
private theorem aux_equivPic_mk0_eq_picMk (I : (Ideal R)⁰) :
    ∃ (_ : Module.Invertible R (I : Ideal R)),
      ClassGroup.equivPic R (ClassGroup.mk0 I) = Pic.mk R (I : Ideal R) := by
  let J := FractionalIdeal.unitsMulEquivSubmodule (FractionalIdeal.mk0 (FractionRing R) I)
  have hJ : J.val = IsLocalization.coeSubmodule (FractionRing R) (I : Ideal R) := by
    change (↑(↑(FractionalIdeal.mk0 (FractionRing R) I) : FractionalIdeal R⁰ (FractionRing R)) :
      Submodule R (FractionRing R)) = _
    rw [FractionalIdeal.coe_mk0, FractionalIdeal.coe_coeIdeal]
  let g := (Algebra.linearMap R (FractionRing R)).comp (I : Ideal R).subtype
  have hg : Function.Injective g :=
    (IsFractionRing.injective R (FractionRing R)).comp (I : Ideal R).subtype_injective
  have hgJ : LinearMap.range g = J.val := by
    rw [hJ, IsLocalization.coeSubmodule, LinearMap.range_comp, Submodule.range_subtype]
  let e : (I : Ideal R) ≃ₗ[R] J := (LinearEquiv.ofInjective g hg).trans
    (LinearEquiv.ofEq _ _ hgJ)
  let : Module.Invertible R (I : Ideal R) := Module.Invertible.congr e.symm
  refine ⟨inferInstance, ?_⟩
  have hPic : ClassGroup.equivPic R (ClassGroup.mk0 I) = Pic.mk R J := by
    rw [ClassGroup.mk0, MonoidHom.comp_apply, ClassGroup.equivPic_apply,
      ← ClassGroup.Quot_mk_eq_mk]
    rfl
  exact hPic.trans (Pic.mk_eq_mk_iff.mpr ⟨e.symm⟩)

theorem solution {R : Type*} [CommRing R] [IsDedekindDomain R]
    (M : Submonoid R) (A : Type*) [CommRing A] [IsDedekindDomain A] [Algebra R A]
    [IsLocalization M A] : Function.Surjective (CommRing.Pic.mapAlgebra R A) := by
  intro x
  obtain ⟨J, hJ⟩ := ClassGroup.mk0_surjective ((ClassGroup.equivPic A).symm x)
  obtain ⟨_, hPicJ⟩ := aux_equivPic_mk0_eq_picMk J
  let I := (J : Ideal A).under R
  have himage : I.map (algebraMap R A) = (J : Ideal A) := IsLocalization.map_under M A J
  have hI : I ≠ ⊥ := by
    intro he
    apply nonZeroDivisors.ne_zero J.property
    rw [← himage, he, Ideal.map_bot]
    rfl
  let I₀ : (Ideal R)⁰ := ⟨I, mem_nonZeroDivisors_iff_ne_zero.mpr hI⟩
  obtain ⟨_, hPicI⟩ := aux_equivPic_mk0_eq_picMk I₀
  let e := (IsLocalizedModule.isBaseChange M A (Algebra.idealMap A I)).equiv.trans
    (LinearEquiv.ofEq _ _ himage)
  refine ⟨ClassGroup.equivPic R (ClassGroup.mk0 I₀), ?_⟩
  calc
    _ = Pic.mapAlgebra R A (Pic.mk R (I₀ : Ideal R)) := congrArg _ hPicI
    _ = Pic.mk A (J : Ideal A) := Pic.mk_eq_mk_iff.mpr
      ⟨(TensorProduct.AlgebraTensorModule.congr (.refl ..) (Pic.mk.linearEquiv ..)) ≪≫ₗ e⟩
    _ = x := hPicJ.symm.trans (by rw [hJ, MulEquiv.apply_symm_apply])

