-- Prove2me | solution 1 for WeierstrassProjModel.exists_ringEquiv_zChartAwayDegreeZero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/73c2309a-9a38-53b8-a32a-a68b3126b15f

import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassProjModel_exists_ringEquiv_zChartAwayDegreeZero

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option Elab.async false

noncomputable section

open MvPolynomial

namespace ProjWeierstrassDehomog

section Maps

variable {R : Type*} [CommRing R]

variable (R) in

noncomputable def dehomogenizeZ : MvPolynomial (Fin 3) R →ₐ[R] Polynomial (Polynomial R) :=
  aeval ![Polynomial.C Polynomial.X, Polynomial.X, 1]

theorem dehomogenizeZ_X_zero : dehomogenizeZ R (X 0) = Polynomial.C Polynomial.X := by
  simp [dehomogenizeZ]

theorem dehomogenizeZ_X_one : dehomogenizeZ R (X 1) = Polynomial.X := by
  simp [dehomogenizeZ]

theorem dehomogenizeZ_X_two : dehomogenizeZ R (X 2) = 1 := by
  simp [dehomogenizeZ]

theorem dehomogenizeZ_C (r : R) :
    dehomogenizeZ R (C r) = Polynomial.C (Polynomial.C r) := by
  simp [dehomogenizeZ]

end Maps

section ChartIdentity

variable {R : Type*} [CommRing R]

theorem aeval_polynomial_eq_toAffine_polynomial (V : WeierstrassCurve.Projective R) :
    aeval (![Polynomial.C Polynomial.X, Polynomial.X, 1] : Fin 3 → Polynomial (Polynomial R))
      V.polynomial = V.toAffine.polynomial := by
  have hC : ∀ r : R,
      aeval (![Polynomial.C Polynomial.X, Polynomial.X, 1] : Fin 3 → Polynomial (Polynomial R))
        (C r) = Polynomial.C (Polynomial.C r) := fun r => by simp
  rw [WeierstrassCurve.Projective.polynomial, WeierstrassCurve.Affine.polynomial]
  simp only [map_add, map_sub, map_mul, map_pow, aeval_X, hC,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  ring

end ChartIdentity

attribute [local instance] MvPolynomial.gradedAlgebra

section GradedPrelim

variable {R : Type*} [CommRing R]

variable (R) in

theorem X_mem_homogeneousSubmodule_one (i : Fin 3) :
    (X i : MvPolynomial (Fin 3) R) ∈ homogeneousSubmodule (Fin 3) R 1 :=
  (mem_homogeneousSubmodule _ _).mpr (isHomogeneous_X _ i)

variable (R) in

theorem C_mem_homogeneousSubmodule_zero (r : R) :
    (C r : MvPolynomial (Fin 3) R) ∈ homogeneousSubmodule (Fin 3) R 0 :=
  (mem_homogeneousSubmodule _ _).mpr (isHomogeneous_C _ _)

variable (R) in

theorem one_mem_homogeneousSubmodule_zero :
    (1 : MvPolynomial (Fin 3) R) ∈ homogeneousSubmodule (Fin 3) R 0 :=
  (mem_homogeneousSubmodule _ _).mpr (isHomogeneous_one _ _)

end GradedPrelim

section ChartElements

variable {R : Type*} [CommRing R]

variable (R) in

def zChartXElem :
    HomogeneousLocalization.Away (homogeneousSubmodule (Fin 3) R)
      (X 2 : MvPolynomial (Fin 3) R) :=
  HomogeneousLocalization.mk
    (⟨1, ⟨X 0, X_mem_homogeneousSubmodule_one R 0⟩, ⟨X 2, X_mem_homogeneousSubmodule_one R 2⟩,
        ⟨1, pow_one _⟩⟩ :
      HomogeneousLocalization.NumDenSameDeg (homogeneousSubmodule (Fin 3) R)
        (Submonoid.powers (X 2 : MvPolynomial (Fin 3) R)))

theorem zChartXElem_val :
    (zChartXElem R).val = Localization.mk (X 0 : MvPolynomial (Fin 3) R)
      (⟨X 2, 1, pow_one _⟩ : Submonoid.powers (X 2 : MvPolynomial (Fin 3) R)) :=
  rfl

variable (R) in

def zChartYElem :
    HomogeneousLocalization.Away (homogeneousSubmodule (Fin 3) R)
      (X 2 : MvPolynomial (Fin 3) R) :=
  HomogeneousLocalization.mk
    (⟨1, ⟨X 1, X_mem_homogeneousSubmodule_one R 1⟩, ⟨X 2, X_mem_homogeneousSubmodule_one R 2⟩,
        ⟨1, pow_one _⟩⟩ :
      HomogeneousLocalization.NumDenSameDeg (homogeneousSubmodule (Fin 3) R)
        (Submonoid.powers (X 2 : MvPolynomial (Fin 3) R)))

theorem zChartYElem_val :
    (zChartYElem R).val = Localization.mk (X 1 : MvPolynomial (Fin 3) R)
      (⟨X 2, 1, pow_one _⟩ : Submonoid.powers (X 2 : MvPolynomial (Fin 3) R)) :=
  rfl

variable (R) in

def zChartConstElem (r : R) :
    HomogeneousLocalization.Away (homogeneousSubmodule (Fin 3) R)
      (X 2 : MvPolynomial (Fin 3) R) :=
  HomogeneousLocalization.mk
    (⟨0, ⟨C r, C_mem_homogeneousSubmodule_zero R r⟩, ⟨1, one_mem_homogeneousSubmodule_zero R⟩,
        ⟨0, pow_zero _⟩⟩ :
      HomogeneousLocalization.NumDenSameDeg (homogeneousSubmodule (Fin 3) R)
        (Submonoid.powers (X 2 : MvPolynomial (Fin 3) R)))

theorem zChartConstElem_val (r : R) :
    (zChartConstElem R r).val
      = Localization.mk (C r : MvPolynomial (Fin 3) R)
          (1 : Submonoid.powers (X 2 : MvPolynomial (Fin 3) R)) :=
  rfl

variable (R) in

def zChartConst :
    R →+* HomogeneousLocalization.Away (homogeneousSubmodule (Fin 3) R)
      (X 2 : MvPolynomial (Fin 3) R) where
  toFun := zChartConstElem R
  map_one' := by
    apply HomogeneousLocalization.val_injective
    rw [HomogeneousLocalization.val_one, zChartConstElem_val, map_one]
    exact Localization.mk_self (1 : Submonoid.powers (X 2 : MvPolynomial (Fin 3) R))
  map_mul' r s := by
    apply HomogeneousLocalization.val_injective
    simp only [HomogeneousLocalization.val_mul, zChartConstElem_val]
    rw [Localization.mk_mul, one_mul, map_mul]
  map_zero' := by
    apply HomogeneousLocalization.val_injective
    rw [HomogeneousLocalization.val_zero, zChartConstElem_val, map_zero, Localization.mk_zero]
  map_add' r s := by
    apply HomogeneousLocalization.val_injective
    simp only [HomogeneousLocalization.val_add, zChartConstElem_val]
    rw [Localization.add_mk_self, map_add]

theorem zChartConst_apply (r : R) : zChartConst R r = zChartConstElem R r :=
  rfl

end ChartElements

section ForwardMap

variable {R : Type*} [CommRing R]

variable (R) in

def dehomogenizeZRingHom : MvPolynomial (Fin 3) R →+* Polynomial (Polynomial R) :=
  (dehomogenizeZ R : MvPolynomial (Fin 3) R →ₐ[R] Polynomial (Polynomial R)).toRingHom

theorem dehomogenizeZRingHom_apply (p : MvPolynomial (Fin 3) R) :
    dehomogenizeZRingHom R p = dehomogenizeZ R p :=
  rfl

theorem dehomogenizeZRingHom_X_two_mul_one :
    dehomogenizeZRingHom R (X 2) * 1 = 1 := by
  rw [dehomogenizeZRingHom_apply, dehomogenizeZ_X_two, mul_one]

variable (R) in

def zChartLocDehom :
    Localization.Away (X 2 : MvPolynomial (Fin 3) R) →+* Polynomial (Polynomial R) :=
  Localization.awayLift (dehomogenizeZRingHom R) (X 2)
    (isUnit_iff_exists_inv.mpr ⟨1, dehomogenizeZRingHom_X_two_mul_one (R := R)⟩)

theorem zChartLocDehom_mk (a : MvPolynomial (Fin 3) R) (n : ℕ) :
    zChartLocDehom R
        (Localization.mk a
          (⟨X 2 ^ n, n, rfl⟩ : Submonoid.powers (X 2 : MvPolynomial (Fin 3) R)))
      = dehomogenizeZ R a := by
  have h := Localization.awayLift_mk (A := Polynomial (Polynomial R)) (dehomogenizeZRingHom R)
    (X 2) a 1 (dehomogenizeZRingHom_X_two_mul_one (R := R)) n
  rw [one_pow, mul_one] at h
  exact h

variable (R) in

def zChartAwayDehom :
    HomogeneousLocalization.Away (homogeneousSubmodule (Fin 3) R)
        (X 2 : MvPolynomial (Fin 3) R) →+*
      Polynomial (Polynomial R) :=
  (zChartLocDehom R).comp
    (algebraMap
      (HomogeneousLocalization.Away (homogeneousSubmodule (Fin 3) R)
        (X 2 : MvPolynomial (Fin 3) R))
      (Localization.Away (X 2 : MvPolynomial (Fin 3) R)))

theorem zChartAwayDehom_awayMk (n : ℕ) (a : MvPolynomial (Fin 3) R)
    (ha : a ∈ homogeneousSubmodule (Fin 3) R (n • 1)) :
    zChartAwayDehom R
        (HomogeneousLocalization.Away.mk (homogeneousSubmodule (Fin 3) R)
          (X_mem_homogeneousSubmodule_one R 2) n a ha)
      = dehomogenizeZ R a := by
  show zChartLocDehom R
      (algebraMap
        (HomogeneousLocalization.Away (homogeneousSubmodule (Fin 3) R)
          (X 2 : MvPolynomial (Fin 3) R))
        (Localization.Away (X 2 : MvPolynomial (Fin 3) R))
        (HomogeneousLocalization.Away.mk (homogeneousSubmodule (Fin 3) R)
          (X_mem_homogeneousSubmodule_one R 2) n a ha))
    = dehomogenizeZ R a
  rw [HomogeneousLocalization.algebraMap_apply]
  have hval : (HomogeneousLocalization.Away.mk (homogeneousSubmodule (Fin 3) R)
        (X_mem_homogeneousSubmodule_one R 2) n a ha).val
      = Localization.mk a
          (⟨X 2 ^ n, n, rfl⟩ : Submonoid.powers (X 2 : MvPolynomial (Fin 3) R)) := rfl
  rw [hval, zChartLocDehom_mk]

theorem zChartAwayDehom_xElem :
    zChartAwayDehom R (zChartXElem R) = Polynomial.C Polynomial.X := by
  show zChartLocDehom R
      (algebraMap
        (HomogeneousLocalization.Away (homogeneousSubmodule (Fin 3) R)
          (X 2 : MvPolynomial (Fin 3) R))
        (Localization.Away (X 2 : MvPolynomial (Fin 3) R)) (zChartXElem R))
    = Polynomial.C Polynomial.X
  rw [HomogeneousLocalization.algebraMap_apply, zChartXElem_val]
  have h1 : (⟨(X 2 : MvPolynomial (Fin 3) R), 1, pow_one _⟩ :
        Submonoid.powers (X 2 : MvPolynomial (Fin 3) R))
      = ⟨X 2 ^ 1, 1, rfl⟩ := Subtype.ext (pow_one _).symm
  rw [h1, zChartLocDehom_mk, dehomogenizeZ_X_zero]

theorem zChartAwayDehom_yElem :
    zChartAwayDehom R (zChartYElem R) = Polynomial.X := by
  show zChartLocDehom R
      (algebraMap
        (HomogeneousLocalization.Away (homogeneousSubmodule (Fin 3) R)
          (X 2 : MvPolynomial (Fin 3) R))
        (Localization.Away (X 2 : MvPolynomial (Fin 3) R)) (zChartYElem R))
    = Polynomial.X
  rw [HomogeneousLocalization.algebraMap_apply, zChartYElem_val]
  have h1 : (⟨(X 2 : MvPolynomial (Fin 3) R), 1, pow_one _⟩ :
        Submonoid.powers (X 2 : MvPolynomial (Fin 3) R))
      = ⟨X 2 ^ 1, 1, rfl⟩ := Subtype.ext (pow_one _).symm
  rw [h1, zChartLocDehom_mk, dehomogenizeZ_X_one]

theorem zChartAwayDehom_const (r : R) :
    zChartAwayDehom R (zChartConst R r) = Polynomial.C (Polynomial.C r) := by
  show zChartLocDehom R
      (algebraMap
        (HomogeneousLocalization.Away (homogeneousSubmodule (Fin 3) R)
          (X 2 : MvPolynomial (Fin 3) R))
        (Localization.Away (X 2 : MvPolynomial (Fin 3) R)) (zChartConst R r))
    = Polynomial.C (Polynomial.C r)
  rw [HomogeneousLocalization.algebraMap_apply, zChartConst_apply, zChartConstElem_val]
  have h1 : (1 : Submonoid.powers (X 2 : MvPolynomial (Fin 3) R)) = ⟨X 2 ^ 0, 0, rfl⟩ :=
    Subtype.ext (pow_zero _).symm
  rw [h1, zChartLocDehom_mk, dehomogenizeZ_C]

end ForwardMap

section BackwardMap

variable {R : Type*} [CommRing R]

variable (R) in

def zChartHomog :
    Polynomial (Polynomial R) →+*
      HomogeneousLocalization.Away (homogeneousSubmodule (Fin 3) R)
        (X 2 : MvPolynomial (Fin 3) R) :=
  Polynomial.eval₂RingHom
    (Polynomial.eval₂RingHom (zChartConst R) (zChartXElem R)) (zChartYElem R)

theorem zChartHomog_X : zChartHomog R Polynomial.X = zChartYElem R := by
  simp [zChartHomog]

theorem zChartHomog_C (p : Polynomial R) :
    zChartHomog R (Polynomial.C p)
      = Polynomial.eval₂RingHom (zChartConst R) (zChartXElem R) p := by
  simp [zChartHomog]

theorem zChartHomog_C_X :
    zChartHomog R (Polynomial.C Polynomial.X) = zChartXElem R := by
  rw [zChartHomog_C]
  simp

theorem zChartHomog_C_C (r : R) :
    zChartHomog R (Polynomial.C (Polynomial.C r)) = zChartConst R r := by
  rw [zChartHomog_C]
  simp

end BackwardMap

section HomogenisationIdentity

variable {R : Type*} [CommRing R]

variable (R) in

def zChartToLoc :
    MvPolynomial (Fin 3) R →+* Localization.Away (X 2 : MvPolynomial (Fin 3) R) :=
  ((algebraMap
      (HomogeneousLocalization.Away (homogeneousSubmodule (Fin 3) R)
        (X 2 : MvPolynomial (Fin 3) R))
      (Localization.Away (X 2 : MvPolynomial (Fin 3) R))).comp (zChartHomog R)).comp
    (dehomogenizeZRingHom R)

theorem zChartToLoc_X_two : zChartToLoc R (X 2) = 1 := by
  show algebraMap
      (HomogeneousLocalization.Away (homogeneousSubmodule (Fin 3) R)
        (X 2 : MvPolynomial (Fin 3) R))
      (Localization.Away (X 2 : MvPolynomial (Fin 3) R))
      (zChartHomog R (dehomogenizeZRingHom R (X 2))) = 1
  rw [dehomogenizeZRingHom_apply, dehomogenizeZ_X_two, map_one, map_one]

theorem zChartToLoc_X_zero :
    zChartToLoc R (X 0)
      = Localization.mk (X 0 : MvPolynomial (Fin 3) R)
          (⟨X 2, 1, pow_one _⟩ : Submonoid.powers (X 2 : MvPolynomial (Fin 3) R)) := by
  show algebraMap
      (HomogeneousLocalization.Away (homogeneousSubmodule (Fin 3) R)
        (X 2 : MvPolynomial (Fin 3) R))
      (Localization.Away (X 2 : MvPolynomial (Fin 3) R))
      (zChartHomog R (dehomogenizeZRingHom R (X 0))) = _
  rw [dehomogenizeZRingHom_apply, dehomogenizeZ_X_zero, zChartHomog_C_X,
    HomogeneousLocalization.algebraMap_apply, zChartXElem_val]

theorem zChartToLoc_X_one :
    zChartToLoc R (X 1)
      = Localization.mk (X 1 : MvPolynomial (Fin 3) R)
          (⟨X 2, 1, pow_one _⟩ : Submonoid.powers (X 2 : MvPolynomial (Fin 3) R)) := by
  show algebraMap
      (HomogeneousLocalization.Away (homogeneousSubmodule (Fin 3) R)
        (X 2 : MvPolynomial (Fin 3) R))
      (Localization.Away (X 2 : MvPolynomial (Fin 3) R))
      (zChartHomog R (dehomogenizeZRingHom R (X 1))) = _
  rw [dehomogenizeZRingHom_apply, dehomogenizeZ_X_one, zChartHomog_X,
    HomogeneousLocalization.algebraMap_apply, zChartYElem_val]

theorem zChartToLoc_C (r : R) :
    zChartToLoc R (C r)
      = algebraMap (MvPolynomial (Fin 3) R)
          (Localization.Away (X 2 : MvPolynomial (Fin 3) R)) (C r) := by
  show algebraMap
      (HomogeneousLocalization.Away (homogeneousSubmodule (Fin 3) R)
        (X 2 : MvPolynomial (Fin 3) R))
      (Localization.Away (X 2 : MvPolynomial (Fin 3) R))
      (zChartHomog R (dehomogenizeZRingHom R (C r))) = _
  rw [dehomogenizeZRingHom_apply, dehomogenizeZ_C, zChartHomog_C_C,
    HomogeneousLocalization.algebraMap_apply, zChartConst_apply, zChartConstElem_val,
    ← Localization.mk_one_eq_algebraMap]

theorem zChartToLoc_X_zero_mul :
    zChartToLoc R (X 0)
        * algebraMap (MvPolynomial (Fin 3) R)
            (Localization.Away (X 2 : MvPolynomial (Fin 3) R)) (X 2)
      = algebraMap (MvPolynomial (Fin 3) R)
          (Localization.Away (X 2 : MvPolynomial (Fin 3) R)) (X 0) := by
  rw [zChartToLoc_X_zero, Localization.mk_eq_mk'_apply]
  exact IsLocalization.mk'_spec (Localization.Away (X 2 : MvPolynomial (Fin 3) R))
    (X 0 : MvPolynomial (Fin 3) R)
    (⟨X 2, 1, pow_one _⟩ : Submonoid.powers (X 2 : MvPolynomial (Fin 3) R))

theorem zChartToLoc_X_one_mul :
    zChartToLoc R (X 1)
        * algebraMap (MvPolynomial (Fin 3) R)
            (Localization.Away (X 2 : MvPolynomial (Fin 3) R)) (X 2)
      = algebraMap (MvPolynomial (Fin 3) R)
          (Localization.Away (X 2 : MvPolynomial (Fin 3) R)) (X 1) := by
  rw [zChartToLoc_X_one, Localization.mk_eq_mk'_apply]
  exact IsLocalization.mk'_spec (Localization.Away (X 2 : MvPolynomial (Fin 3) R))
    (X 1 : MvPolynomial (Fin 3) R)
    (⟨X 2, 1, pow_one _⟩ : Submonoid.powers (X 2 : MvPolynomial (Fin 3) R))

theorem monomial_eq_C_mul_pow (d : Fin 3 →₀ ℕ) (c : R) :
    (monomial d c : MvPolynomial (Fin 3) R)
      = C c * (X 0 ^ d 0 * X 1 ^ d 1 * X 2 ^ d 2) := by
  rw [MvPolynomial.monomial_eq, Finsupp.prod_fintype _ _ fun i => pow_zero _,
    Fin.prod_univ_three]

theorem zChartToLoc_monomial (d : Fin 3 →₀ ℕ) (c : R) (n : ℕ)
    (hn : d 0 + d 1 + d 2 = n) :
    zChartToLoc R (monomial d c)
      = Localization.mk (monomial d c)
          (⟨X 2 ^ n, n, rfl⟩ : Submonoid.powers (X 2 : MvPolynomial (Fin 3) R)) := by
  rw [Localization.mk_eq_mk'_apply, IsLocalization.eq_mk'_iff_mul_eq]
  show zChartToLoc R (monomial d c)
        * algebraMap (MvPolynomial (Fin 3) R)
            (Localization.Away (X 2 : MvPolynomial (Fin 3) R)) (X 2 ^ n)
      = algebraMap (MvPolynomial (Fin 3) R)
          (Localization.Away (X 2 : MvPolynomial (Fin 3) R)) (monomial d c)
  rw [monomial_eq_C_mul_pow]
  simp only [map_mul, map_pow]
  rw [zChartToLoc_C, zChartToLoc_X_two, one_pow, mul_one, ← hn, pow_add, pow_add,
    ← zChartToLoc_X_zero_mul, ← zChartToLoc_X_one_mul, mul_pow, mul_pow]
  ring

theorem zChartToLoc_isHomogeneous (n : ℕ) (a : MvPolynomial (Fin 3) R)
    (ha : a.IsHomogeneous n) :
    zChartToLoc R a
      = Localization.mk a
          (⟨X 2 ^ n, n, rfl⟩ : Submonoid.powers (X 2 : MvPolynomial (Fin 3) R)) := by
  conv_lhs => rw [MvPolynomial.as_sum a]
  conv_rhs => rw [MvPolynomial.as_sum a]
  rw [map_sum, Localization.mk_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdeg : d.degree = n := by
    by_contra hne
    exact MvPolynomial.mem_support_iff.mp hd (ha.coeff_eq_zero hne)
  exact zChartToLoc_monomial d (MvPolynomial.coeff d a) n
    (by rw [← hdeg, Finsupp.degree_eq_sum, Fin.sum_univ_three])

end HomogenisationIdentity

section CompositeIdentities

variable {R : Type*} [CommRing R]

theorem zChartAwayDehom_comp_zChartHomog :
    (zChartAwayDehom R).comp (zChartHomog R) = RingHom.id (Polynomial (Polynomial R)) := by
  have hCC : ∀ r : R, zChartAwayDehom R (zChartHomog R (Polynomial.C (Polynomial.C r)))
      = Polynomial.C (Polynomial.C r) := fun r => by
    rw [zChartHomog_C_C, zChartAwayDehom_const]
  have hCX : zChartAwayDehom R (zChartHomog R (Polynomial.C Polynomial.X))
      = Polynomial.C Polynomial.X := by
    rw [zChartHomog_C_X, zChartAwayDehom_xElem]
  have hX : zChartAwayDehom R (zChartHomog R Polynomial.X) = Polynomial.X := by
    rw [zChartHomog_X, zChartAwayDehom_yElem]
  refine Polynomial.ringHom_ext (fun p => ?_) ?_
  · rw [RingHom.comp_apply, RingHom.id_apply]
    have hcomp : ((zChartAwayDehom R).comp (zChartHomog R)).comp
          (Polynomial.C : Polynomial R →+* Polynomial (Polynomial R))
        = (Polynomial.C : Polynomial R →+* Polynomial (Polynomial R)) := by
      refine Polynomial.ringHom_ext (fun r => ?_) ?_
      · rw [RingHom.comp_apply, RingHom.comp_apply]
        exact hCC r
      · rw [RingHom.comp_apply, RingHom.comp_apply]
        exact hCX
    have h := RingHom.congr_fun hcomp p
    rwa [RingHom.comp_apply, RingHom.comp_apply] at h
  · rw [RingHom.comp_apply, RingHom.id_apply]
    exact hX

theorem zChartHomog_comp_zChartAwayDehom :
    (zChartHomog R).comp (zChartAwayDehom R)
      = RingHom.id (HomogeneousLocalization.Away (homogeneousSubmodule (Fin 3) R)
          (X 2 : MvPolynomial (Fin 3) R)) := by
  refine RingHom.ext fun z => ?_
  obtain ⟨n, a, ha, rfl⟩ := HomogeneousLocalization.Away.mk_surjective
    (homogeneousSubmodule (Fin 3) R) (X_mem_homogeneousSubmodule_one R 2) z
  apply HomogeneousLocalization.val_injective
  rw [RingHom.comp_apply, RingHom.id_apply, zChartAwayDehom_awayMk]
  show zChartToLoc R a
      = Localization.mk a
          (⟨X 2 ^ n, n, rfl⟩ : Submonoid.powers (X 2 : MvPolynomial (Fin 3) R))
  exact zChartToLoc_isHomogeneous n a
    ((MvPolynomial.mem_homogeneousSubmodule n a).mp (by simpa using ha))

end CompositeIdentities

section Isomorphisms

variable {R : Type*} [CommRing R]

variable (R) in

def zChartPolyEquiv :
    HomogeneousLocalization.Away (homogeneousSubmodule (Fin 3) R)
        (X 2 : MvPolynomial (Fin 3) R) ≃+*
      Polynomial (Polynomial R) :=
  RingEquiv.ofRingHom (zChartAwayDehom R) (zChartHomog R)
    zChartAwayDehom_comp_zChartHomog zChartHomog_comp_zChartAwayDehom

theorem zChartPolyEquiv_apply
    (z : HomogeneousLocalization.Away (homogeneousSubmodule (Fin 3) R)
      (X 2 : MvPolynomial (Fin 3) R)) :
    zChartPolyEquiv R z = zChartAwayDehom R z :=
  rfl

end Isomorphisms

end ProjWeierstrassDehomog

end

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra in
theorem solution (R : Type) [CommRing R] :
    (∃ e : HomogeneousLocalization.Away (homogeneousSubmodule (Fin 3) R)
          (X 2 : MvPolynomial (Fin 3) R) ≃+*
        Polynomial (Polynomial R),
      ∀ (n : ℕ) (a : MvPolynomial (Fin 3) R)
        (ha : a ∈ homogeneousSubmodule (Fin 3) R (n • 1)),
        e (HomogeneousLocalization.Away.mk (homogeneousSubmodule (Fin 3) R)
            ((mem_homogeneousSubmodule _ _).mpr (isHomogeneous_X _ 2)) n a ha)
          = aeval (![Polynomial.C Polynomial.X, Polynomial.X, 1] :
              Fin 3 → Polynomial (Polynomial R)) a) ∧
    ∀ (V : WeierstrassCurve.Projective R),
      aeval (![Polynomial.C Polynomial.X, Polynomial.X, 1] :
          Fin 3 → Polynomial (Polynomial R)) V.polynomial
        = V.toAffine.polynomial :=
  ⟨⟨ProjWeierstrassDehomog.zChartPolyEquiv R, fun n a ha => by
      rw [ProjWeierstrassDehomog.zChartPolyEquiv_apply]
      exact ProjWeierstrassDehomog.zChartAwayDehom_awayMk n a ha⟩,
    fun V => ProjWeierstrassDehomog.aeval_polynomial_eq_toAffine_polynomial V⟩

end S_WeierstrassProjModel_exists_ringEquiv_zChartAwayDegreeZero
end P2MW
export P2MW.S_WeierstrassProjModel_exists_ringEquiv_zChartAwayDegreeZero (solution)
