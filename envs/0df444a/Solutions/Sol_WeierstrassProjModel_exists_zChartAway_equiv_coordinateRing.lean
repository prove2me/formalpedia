-- Prove2me | solution 1 for WeierstrassProjModel.exists_zChartAway_equiv_coordinateRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/f7e8b35f-f974-52a5-87d7-433095007219

import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Theorems.Thm_WeierstrassProjModel_exists_ringEquiv_zChartAwayDegreeZero_univ
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Basic
import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.Localization.Away.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassProjModel_exists_zChartAway_equiv_coordinateRing

universe u

set_option Elab.async false

section MEGA_prelude_z_lean

end MEGA_prelude_z_lean

section MEGA_ProjectiveWeierstrassDehomogenisationA1_lean

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

theorem dehomogenizeZ_polynomial (V : WeierstrassCurve.Projective R) :
    dehomogenizeZ R V.polynomial = V.toAffine.polynomial :=
  aeval_polynomial_eq_toAffine_polynomial V

end ChartIdentity

section InfinityIdentity

variable {R : Type*} [CommRing R]

end InfinityIdentity

section PointDictionary

variable {R : Type*} [CommRing R]

end PointDictionary

end ProjWeierstrassDehomog

end MEGA_ProjectiveWeierstrassDehomogenisationA1_lean

section MEGA_ZcadShim_lean

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open MvPolynomial

namespace ProjWeierstrassDehomog

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

section ServedEquiv

variable (R : Type u) [CommRing R]

noncomputable def zChartPolyEquiv :
    HomogeneousLocalization.Away (homogeneousSubmodule (Fin 3) R)
        (X 2 : MvPolynomial (Fin 3) R) ≃+*
      Polynomial (Polynomial R) :=
  (WeierstrassProjModel.exists_ringEquiv_zChartAwayDegreeZero_univ R).1.choose

noncomputable def zChartAwayDehom :
    HomogeneousLocalization.Away (homogeneousSubmodule (Fin 3) R)
        (X 2 : MvPolynomial (Fin 3) R) →+*
      Polynomial (Polynomial R) :=
  (zChartPolyEquiv R).toRingHom

variable {R} in
theorem zChartPolyEquiv_apply
    (z : HomogeneousLocalization.Away (homogeneousSubmodule (Fin 3) R)
      (X 2 : MvPolynomial (Fin 3) R)) :
    zChartPolyEquiv R z = zChartAwayDehom R z :=
  rfl

variable {R} in

theorem zChartAwayDehom_awayMk (n : ℕ) (a : MvPolynomial (Fin 3) R)
    (ha : a ∈ homogeneousSubmodule (Fin 3) R (n • 1)) :
    zChartAwayDehom R
        (HomogeneousLocalization.Away.mk (homogeneousSubmodule (Fin 3) R)
          (X_mem_homogeneousSubmodule_one R 2) n a ha)
      = dehomogenizeZ R a :=
  (WeierstrassProjModel.exists_ringEquiv_zChartAwayDegreeZero_univ R).1.choose_spec n a ha

variable {R} in

theorem zChartConst_eq_awayMk (r : R) :
    zChartConst R r
      = HomogeneousLocalization.Away.mk (homogeneousSubmodule (Fin 3) R)
          (X_mem_homogeneousSubmodule_one R 2) 0 (C r)
          (by simp) := by
  apply HomogeneousLocalization.val_injective
  rw [zChartConst_apply, zChartConstElem_val, HomogeneousLocalization.Away.val_mk]
  exact congrArg (Localization.mk (C r : MvPolynomial (Fin 3) R)) (Subtype.ext (pow_zero _).symm)

variable {R} in

theorem zChartAwayDehom_const (r : R) :
    zChartAwayDehom R (zChartConst R r) = Polynomial.C (Polynomial.C r) := by
  rw [zChartConst_eq_awayMk, zChartAwayDehom_awayMk, dehomogenizeZ_C]

end ServedEquiv

end ProjWeierstrassDehomog

end
end MEGA_ZcadShim_lean

section MEGA_KwNo3aWdpMprtZChartSmoothCRDischarge_lean

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousIdealQuotientGrading
open ProjWeierstrassCubicPrime HomogeneousLocalization

namespace WeierstrassProjModel
p2m_export "WeierstrassProjModel" "projModelHomogeneousIdealCR projModelHomogeneousIdealCR_toIdeal projModelGradingCR exists_ringEquiv_zChartAwayDegreeZero_univ"
p2m_open "WeierstrassProjModel"

attribute [local instance] MvPolynomial.gradedAlgebra

variable {R : Type u} [CommRing R]

def kw_no3a_wdp_mprt_zcdCR_fromR (V : WeierstrassCurve.Projective R) (i : Fin 3) :
    R →+* HomogeneousLocalization.Away (projModelGradingCR V)
      (Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal
        (X i : MvPolynomial (Fin 3) R)) :=
  (HomogeneousLocalization.fromZeroRingHom (projModelGradingCR V)
      (Submonoid.powers (Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal
        (X i : MvPolynomial (Fin 3) R)))).comp
    (algebraMap R ((projModelGradingCR V) 0))

end WeierstrassProjModel

end

end MEGA_KwNo3aWdpMprtZChartSmoothCRDischarge_lean

section MEGA_KwNo3aWdpMprtZBridgeCRDischarge_lean

set_option autoImplicit false

set_option maxHeartbeats 32000000
set_option linter.unusedSectionVars false

noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousIdealQuotientGrading
open ProjWeierstrassCubicPrime ProjWeierstrassDehomog

namespace WeierstrassProjModel
p2m_export "WeierstrassProjModel" "projModelHomogeneousIdealCR projModelHomogeneousIdealCR_toIdeal projModelGradingCR exists_ringEquiv_zChartAwayDegreeZero_univ"
p2m_open "WeierstrassProjModel"

attribute [local instance] MvPolynomial.gradedAlgebra

variable {R : Type u} [CommRing R]

def kw_no3a_wdp_mprt_aqcCR_quotGradedRingHom (V : WeierstrassCurve.Projective R) :
    (homogeneousSubmodule (Fin 3) R) →+*ᵍ (projModelGradingCR V) where
  toRingHom := Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal
  map_mem ha := mk_mem_quotGradingSubmodule _ _ ha

def kw_no3a_wdp_mprt_aqcCR_q (V : WeierstrassCurve.Projective R) (i : Fin 3) :
    HomogeneousLocalization.Away (homogeneousSubmodule (Fin 3) R)
        (X i : MvPolynomial (Fin 3) R) →+*
      HomogeneousLocalization.Away (projModelGradingCR V)
        (Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal
          (X i : MvPolynomial (Fin 3) R)) :=
  HomogeneousLocalization.Away.map (kw_no3a_wdp_mprt_aqcCR_quotGradedRingHom V) (X i)

theorem kw_no3a_wdp_mprt_aqcCR_mkX_mem_one (V : WeierstrassCurve.Projective R) (i : Fin 3) :
    Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal (X i : MvPolynomial (Fin 3) R)
      ∈ projModelGradingCR V 1 :=
  mk_mem_quotGradingSubmodule _ _ (X_mem_homogeneousSubmodule_one R i)

theorem kw_no3a_wdp_mprt_aqcCR_q_awayMk (V : WeierstrassCurve.Projective R) (i : Fin 3)
    (n : ℕ) (b : MvPolynomial (Fin 3) R) (hb : b ∈ homogeneousSubmodule (Fin 3) R (n • 1)) :
    kw_no3a_wdp_mprt_aqcCR_q V i
        (HomogeneousLocalization.Away.mk (homogeneousSubmodule (Fin 3) R)
          (X_mem_homogeneousSubmodule_one R i) n b hb)
      = HomogeneousLocalization.Away.mk (projModelGradingCR V)
          (kw_no3a_wdp_mprt_aqcCR_mkX_mem_one V i) n
          (Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal b)
          (mk_mem_quotGradingSubmodule _ _ hb) :=
  HomogeneousLocalization.Away.map_mk (kw_no3a_wdp_mprt_aqcCR_quotGradedRingHom V) (X i)
    (X_mem_homogeneousSubmodule_one R i) n b hb

theorem kw_no3a_wdp_mprt_aqcCR_Vpoly_mem (V : WeierstrassCurve.Projective R) :
    V.polynomial ∈ homogeneousSubmodule (Fin 3) R (3 • 1) := by
  rw [smul_eq_mul, mul_one]
  exact (mem_homogeneousSubmodule _ _).mpr (isHomogeneous_polynomial V)

def kw_no3a_wdp_mprt_aqcCR_W_loc (V : WeierstrassCurve.Projective R) (i : Fin 3) :
    HomogeneousLocalization.Away (homogeneousSubmodule (Fin 3) R)
      (X i : MvPolynomial (Fin 3) R) :=
  HomogeneousLocalization.Away.mk (homogeneousSubmodule (Fin 3) R)
    (X_mem_homogeneousSubmodule_one R i) 3 V.polynomial (kw_no3a_wdp_mprt_aqcCR_Vpoly_mem V)

def kw_no3a_wdp_mprt_aqcCR_ambientFromRElem (i : Fin 3) (r : R) :
    HomogeneousLocalization.Away (homogeneousSubmodule (Fin 3) R)
      (X i : MvPolynomial (Fin 3) R) :=
  HomogeneousLocalization.mk
    ⟨0, ⟨C r, C_mem_homogeneousSubmodule_zero R r⟩, ⟨1, one_mem_homogeneousSubmodule_zero R⟩,
      ⟨0, pow_zero _⟩⟩

theorem kw_no3a_wdp_mprt_aqcCR_ambientFromRElem_val (i : Fin 3) (r : R) :
    (kw_no3a_wdp_mprt_aqcCR_ambientFromRElem i r).val
      = Localization.mk (C r : MvPolynomial (Fin 3) R)
          (1 : Submonoid.powers (X i : MvPolynomial (Fin 3) R)) :=
  rfl

def kw_no3a_wdp_mprt_aqcCR_ambientFromR (_V : WeierstrassCurve.Projective R) (i : Fin 3) :
    R →+* HomogeneousLocalization.Away (homogeneousSubmodule (Fin 3) R)
      (X i : MvPolynomial (Fin 3) R) where
  toFun := kw_no3a_wdp_mprt_aqcCR_ambientFromRElem i
  map_one' := by
    rw [HomogeneousLocalization.ext_iff_val, HomogeneousLocalization.val_one,
      kw_no3a_wdp_mprt_aqcCR_ambientFromRElem_val, map_one]
    exact Localization.mk_self (1 : Submonoid.powers (X i : MvPolynomial (Fin 3) R))
  map_mul' r s := by
    rw [HomogeneousLocalization.ext_iff_val, HomogeneousLocalization.val_mul,
      kw_no3a_wdp_mprt_aqcCR_ambientFromRElem_val, kw_no3a_wdp_mprt_aqcCR_ambientFromRElem_val,
      kw_no3a_wdp_mprt_aqcCR_ambientFromRElem_val, Localization.mk_mul, mul_one, map_mul]
  map_zero' := by
    rw [HomogeneousLocalization.ext_iff_val, HomogeneousLocalization.val_zero,
      kw_no3a_wdp_mprt_aqcCR_ambientFromRElem_val, map_zero, Localization.mk_zero]
  map_add' r s := by
    rw [HomogeneousLocalization.ext_iff_val, HomogeneousLocalization.val_add,
      kw_no3a_wdp_mprt_aqcCR_ambientFromRElem_val, kw_no3a_wdp_mprt_aqcCR_ambientFromRElem_val,
      kw_no3a_wdp_mprt_aqcCR_ambientFromRElem_val, Localization.add_mk_self, map_add]

theorem kw_no3a_wdp_mprt_aqcCR_ambientFromR_two (V : WeierstrassCurve.Projective R) :
    kw_no3a_wdp_mprt_aqcCR_ambientFromR V 2 = zChartConst R :=
  rfl

noncomputable def kw_no3a_wdp_mprt_aqcCR_liftOfSurjective {A B C : Type*} [CommRing A]
    [CommRing B] [CommRing C] (f : A →+* B) (hf : Function.Surjective f) (g : A →+* C)
    (H : RingHom.ker f ≤ RingHom.ker g) : B →+* C :=
  (Ideal.Quotient.lift _ g (fun _ ha => RingHom.mem_ker.mp (H ha))).comp
    (RingHom.quotientKerEquivOfSurjective hf).symm.toRingHom

theorem kw_no3a_wdp_mprt_aqcCR_liftOfSurjective_comp {A B C : Type*} [CommRing A] [CommRing B]
    [CommRing C] (f : A →+* B) (hf : Function.Surjective f) (g : A →+* C)
    (H : RingHom.ker f ≤ RingHom.ker g) :
    (kw_no3a_wdp_mprt_aqcCR_liftOfSurjective f hf g H).comp f = g := by
  unfold kw_no3a_wdp_mprt_aqcCR_liftOfSurjective
  rw [RingHom.comp_assoc, RingHom.quotientKerEquivOfSurjective_symm_comp]
  exact Ideal.Quotient.lift_comp_mk _ _ _

theorem kw_no3a_wdp_mprt_aqcCR_liftOfSurjective_apply {A B C : Type*} [CommRing A] [CommRing B]
    [CommRing C] (f : A →+* B) (hf : Function.Surjective f) (g : A →+* C)
    (H : RingHom.ker f ≤ RingHom.ker g) (a : A) :
    kw_no3a_wdp_mprt_aqcCR_liftOfSurjective f hf g H (f a) = g a :=
  RingHom.congr_fun (kw_no3a_wdp_mprt_aqcCR_liftOfSurjective_comp f hf g H) a

theorem kw_no3a_wdp_mprt_aqcCR_liftOfSurjective_bijective {A B C : Type*} [CommRing A]
    [CommRing B] [CommRing C] (f : A →+* B) (hf : Function.Surjective f) (g : A →+* C)
    (hg : Function.Surjective g) (H : RingHom.ker f = RingHom.ker g) :
    Function.Bijective (kw_no3a_wdp_mprt_aqcCR_liftOfSurjective f hf g (le_of_eq H)) := by
  refine ⟨?_, ?_⟩
  · intro b₁ b₂ hb
    obtain ⟨a₁, rfl⟩ := hf b₁
    obtain ⟨a₂, rfl⟩ := hf b₂
    rw [kw_no3a_wdp_mprt_aqcCR_liftOfSurjective_apply,
      kw_no3a_wdp_mprt_aqcCR_liftOfSurjective_apply] at hb
    have hker : a₁ - a₂ ∈ RingHom.ker g := by
      rw [RingHom.mem_ker, map_sub, hb, sub_self]
    rw [← H] at hker
    have hsub : f a₁ - f a₂ = 0 := by rw [← map_sub]; exact RingHom.mem_ker.mp hker
    exact sub_eq_zero.mp hsub
  · intro c
    obtain ⟨a, rfl⟩ := hg c
    exact ⟨f a, kw_no3a_wdp_mprt_aqcCR_liftOfSurjective_apply f hf g _ a⟩

theorem kw_no3a_wdp_mprt_aqcCR_q_surjective (V : WeierstrassCurve.Projective R) (i : Fin 3) :
    Function.Surjective (kw_no3a_wdp_mprt_aqcCR_q V i) := by
  intro y
  obtain ⟨n, a, ha, rfl⟩ :=
    HomogeneousLocalization.Away.mk_surjective (projModelGradingCR V)
      (kw_no3a_wdp_mprt_aqcCR_mkX_mem_one V i) y
  obtain ⟨b, hb, rfl⟩ := (mem_quotGradingSubmodule_iff _ _).mp ha
  exact ⟨HomogeneousLocalization.Away.mk (homogeneousSubmodule (Fin 3) R)
    (X_mem_homogeneousSubmodule_one R i) n b hb, kw_no3a_wdp_mprt_aqcCR_q_awayMk V i n b hb⟩

theorem kw_no3a_wdp_mprt_aqcCR_q_W_loc_eq_zero (V : WeierstrassCurve.Projective R)
    (i : Fin 3) :
    kw_no3a_wdp_mprt_aqcCR_q V i (kw_no3a_wdp_mprt_aqcCR_W_loc V i) = 0 := by
  have hzero : Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal V.polynomial = 0 := by
    rw [Ideal.Quotient.eq_zero_iff_mem, projModelHomogeneousIdealCR_toIdeal]
    exact Ideal.mem_span_singleton_self _
  rw [kw_no3a_wdp_mprt_aqcCR_W_loc, kw_no3a_wdp_mprt_aqcCR_q_awayMk,
    HomogeneousLocalization.ext_iff_val, HomogeneousLocalization.val_zero,
    HomogeneousLocalization.Away.val_mk, hzero, Localization.mk_zero]

theorem kw_no3a_wdp_mprt_aqcCR_homogeneousCofactor (V : WeierstrassCurve.Projective R)
    (i : Fin 3) {m n : ℕ} (b : MvPolynomial (Fin 3) R)
    (hb : b ∈ homogeneousSubmodule (Fin 3) R n) (hmn : m + n ≥ 3)
    (hmem : (X i : MvPolynomial (Fin 3) R) ^ m * b ∈ Ideal.span {V.polynomial}) :
    ∃ p' ∈ homogeneousSubmodule (Fin 3) R (m + n - 3),
      (X i : MvPolynomial (Fin 3) R) ^ m * b = V.polynomial * p' := by
  classical
  rw [Ideal.mem_span_singleton'] at hmem
  obtain ⟨p, hp⟩ := hmem
  refine ⟨(DirectSum.decompose (homogeneousSubmodule (Fin 3) R) p (m + n - 3) :
      MvPolynomial (Fin 3) R),
    (DirectSum.decompose (homogeneousSubmodule (Fin 3) R) p (m + n - 3)).2, ?_⟩
  have hVmem : V.polynomial ∈ homogeneousSubmodule (Fin 3) R 3 :=
    (mem_homogeneousSubmodule _ _).mpr (isHomogeneous_polynomial V)
  have hprodmem : (X i : MvPolynomial (Fin 3) R) ^ m * b
      ∈ homogeneousSubmodule (Fin 3) R (m + n) := by
    have hXm : ((X i : MvPolynomial (Fin 3) R) ^ m).IsHomogeneous m :=
      isHomogeneous_X_pow i m
    exact (mem_homogeneousSubmodule _ _).mpr
      (hXm.mul ((mem_homogeneousSubmodule _ _).mp hb))
  have key : (DirectSum.decompose (homogeneousSubmodule (Fin 3) R)
        (V.polynomial * p) (3 + (m + n - 3)) : MvPolynomial (Fin 3) R)
      = V.polynomial * (DirectSum.decompose (homogeneousSubmodule (Fin 3) R) p (m + n - 3) :
          MvPolynomial (Fin 3) R) :=
    DirectSum.coe_decompose_mul_add_of_left_mem (homogeneousSubmodule (Fin 3) R) hVmem
  have harith : 3 + (m + n - 3) = m + n := Nat.add_sub_cancel' hmn
  rw [harith, mul_comm V.polynomial p, hp,
    DirectSum.decompose_of_mem_same (homogeneousSubmodule (Fin 3) R) hprodmem] at key
  exact key

theorem kw_no3a_wdp_mprt_aqcCR_ker_q_le_span (V : WeierstrassCurve.Projective R) (i : Fin 3) :
    RingHom.ker (kw_no3a_wdp_mprt_aqcCR_q V i)
      ≤ Ideal.span {kw_no3a_wdp_mprt_aqcCR_W_loc V i} := by
  classical
  intro x hx
  obtain ⟨n, b, hb, rfl⟩ :=
    HomogeneousLocalization.Away.mk_surjective (homogeneousSubmodule (Fin 3) R)
      (X_mem_homogeneousSubmodule_one R i) x
  rw [RingHom.mem_ker, kw_no3a_wdp_mprt_aqcCR_q_awayMk, HomogeneousLocalization.ext_iff_val,
    HomogeneousLocalization.val_zero, HomogeneousLocalization.Away.val_mk,
    Localization.mk_eq_mk'_apply, IsLocalization.mk'_eq_zero_iff] at hx
  obtain ⟨⟨c, m₀, hc⟩, hann⟩ := hx
  have hann2 : (Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal
      (X i : MvPolynomial (Fin 3) R)) ^ m₀ *
      Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal b = 0 := by
    simpa only [← hc] using hann
  set m := m₀ + 3 with hm_def
  have hmn : m + n ≥ 3 := le_trans (Nat.le_add_left 3 m₀) (Nat.le_add_right _ n)
  have hann' : (X i : MvPolynomial (Fin 3) R) ^ m * b ∈ Ideal.span {V.polynomial} := by
    rw [← projModelHomogeneousIdealCR_toIdeal, ← Ideal.Quotient.eq_zero_iff_mem]
    calc Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal
            ((X i : MvPolynomial (Fin 3) R) ^ m * b)
        = (Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal
              (X i : MvPolynomial (Fin 3) R)) ^ 3
            * ((Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal
                (X i : MvPolynomial (Fin 3) R)) ^ m₀
              * Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal b) := by
          rw [map_mul, map_pow, hm_def]; ring
      _ = 0 := by rw [hann2, mul_zero]
  have hbn : b ∈ homogeneousSubmodule (Fin 3) R n := by
    have := hb; rw [smul_eq_mul, mul_one] at this; exact this
  obtain ⟨p', hp'_mem, hp'_eq⟩ :=
    kw_no3a_wdp_mprt_aqcCR_homogeneousCofactor V i b hbn hmn hann'
  have hp'_mem' : p' ∈ homogeneousSubmodule (Fin 3) R ((m + n - 3) • 1) := by
    rw [smul_eq_mul, mul_one]; exact hp'_mem
  refine Ideal.mem_span_singleton'.mpr
    ⟨HomogeneousLocalization.Away.mk (homogeneousSubmodule (Fin 3) R)
      (X_mem_homogeneousSubmodule_one R i) (m + n - 3) p' hp'_mem', ?_⟩
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.val_mul, HomogeneousLocalization.Away.val_mk,
    kw_no3a_wdp_mprt_aqcCR_W_loc, HomogeneousLocalization.Away.val_mk,
    HomogeneousLocalization.Away.val_mk, Localization.mk_mul]
  rw [show ((⟨(X i : MvPolynomial (Fin 3) R) ^ (m + n - 3), m + n - 3, rfl⟩ :
        Submonoid.powers (X i : MvPolynomial (Fin 3) R)) *
      ⟨(X i : MvPolynomial (Fin 3) R) ^ 3, 3, rfl⟩)
    = ⟨(X i : MvPolynomial (Fin 3) R) ^ (m + n), m + n, rfl⟩ from
      Subtype.ext (by simp only [Submonoid.coe_mul]; rw [← pow_add, Nat.sub_add_cancel hmn])]
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [OneMemClass.coe_one, one_mul]
  rw [mul_comm p' V.polynomial, ← hp'_eq]
  ring

theorem kw_no3a_wdp_mprt_aqcCR_ker_q_eq_span (V : WeierstrassCurve.Projective R) (i : Fin 3) :
    RingHom.ker (kw_no3a_wdp_mprt_aqcCR_q V i)
      = Ideal.span {kw_no3a_wdp_mprt_aqcCR_W_loc V i} :=
  le_antisymm (kw_no3a_wdp_mprt_aqcCR_ker_q_le_span V i)
    (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr
      (RingHom.mem_ker.mpr (kw_no3a_wdp_mprt_aqcCR_q_W_loc_eq_zero V i))))

theorem kw_no3a_wdp_mprt_aqcCR_fromR_val (V : WeierstrassCurve.Projective R) (i : Fin 3)
    (r : R) :
    (kw_no3a_wdp_mprt_zcdCR_fromR V i r).val
      = Localization.mk (Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal (C r))
          (1 : Submonoid.powers (Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal
            (X i : MvPolynomial (Fin 3) R))) :=
  rfl

theorem kw_no3a_wdp_mprt_aqcCR_q_comp_ambientFromR (V : WeierstrassCurve.Projective R)
    (i : Fin 3) :
    (kw_no3a_wdp_mprt_aqcCR_q V i).comp (kw_no3a_wdp_mprt_aqcCR_ambientFromR V i)
      = kw_no3a_wdp_mprt_zcdCR_fromR V i := by
  refine RingHom.ext fun r => ?_
  rw [HomogeneousLocalization.ext_iff_val, kw_no3a_wdp_mprt_aqcCR_fromR_val, RingHom.comp_apply]
  simp only [kw_no3a_wdp_mprt_aqcCR_q, kw_no3a_wdp_mprt_aqcCR_ambientFromR, RingHom.coe_mk,
    MonoidHom.coe_mk, OneHom.coe_mk, kw_no3a_wdp_mprt_aqcCR_ambientFromRElem,
    HomogeneousLocalization.Away.map]
  rfl

def kw_no3a_wdp_mprt_aqcCR_zAP (V : WeierstrassCurve.Projective R) :
    HomogeneousLocalization.Away (homogeneousSubmodule (Fin 3) R)
        (X 2 : MvPolynomial (Fin 3) R) →+*
      (Polynomial (Polynomial R) ⧸ Ideal.span {V.toAffine.polynomial}) :=
  (Ideal.Quotient.mk (Ideal.span {V.toAffine.polynomial})).comp (zChartAwayDehom R)

theorem kw_no3a_wdp_mprt_aqcCR_zAP_surjective (V : WeierstrassCurve.Projective R) :
    Function.Surjective (kw_no3a_wdp_mprt_aqcCR_zAP V) := by
  intro y
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective y
  exact ⟨(zChartPolyEquiv R).symm p, by
    rw [kw_no3a_wdp_mprt_aqcCR_zAP, RingHom.comp_apply, ← zChartPolyEquiv_apply,
      RingEquiv.apply_symm_apply]⟩

theorem kw_no3a_wdp_mprt_aqcCR_zAP_W_loc (V : WeierstrassCurve.Projective R) :
    kw_no3a_wdp_mprt_aqcCR_zAP V (kw_no3a_wdp_mprt_aqcCR_W_loc V 2) = 0 := by
  unfold kw_no3a_wdp_mprt_aqcCR_zAP kw_no3a_wdp_mprt_aqcCR_W_loc
  rw [RingHom.comp_apply, zChartAwayDehom_awayMk, dehomogenizeZ_polynomial,
    Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mem_span_singleton_self _

theorem kw_no3a_wdp_mprt_aqcCR_ker_zAP (V : WeierstrassCurve.Projective R) :
    RingHom.ker (kw_no3a_wdp_mprt_aqcCR_zAP V)
      = Ideal.span {kw_no3a_wdp_mprt_aqcCR_W_loc V 2} := by
  have hW : zChartAwayDehom R (kw_no3a_wdp_mprt_aqcCR_W_loc V 2) = V.toAffine.polynomial := by
    unfold kw_no3a_wdp_mprt_aqcCR_W_loc
    rw [zChartAwayDehom_awayMk, dehomogenizeZ_polynomial]
  refine le_antisymm ?_ (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr
    (RingHom.mem_ker.mpr (kw_no3a_wdp_mprt_aqcCR_zAP_W_loc V))))
  intro x hx
  rw [RingHom.mem_ker, kw_no3a_wdp_mprt_aqcCR_zAP, RingHom.comp_apply,
    Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton'] at hx
  obtain ⟨q, hq⟩ := hx
  refine Ideal.mem_span_singleton'.mpr ⟨(zChartPolyEquiv R).symm q, ?_⟩
  apply (zChartPolyEquiv R).injective
  rw [map_mul, RingEquiv.apply_symm_apply, zChartPolyEquiv_apply, hW, zChartPolyEquiv_apply, hq]

theorem kw_no3a_wdp_mprt_aqcCR_zAP_comp_ambientFromR (V : WeierstrassCurve.Projective R) :
    (kw_no3a_wdp_mprt_aqcCR_zAP V).comp (kw_no3a_wdp_mprt_aqcCR_ambientFromR V 2)
      = algebraMap R (Polynomial (Polynomial R) ⧸ Ideal.span {V.toAffine.polynomial}) := by
  rw [kw_no3a_wdp_mprt_aqcCR_ambientFromR_two]
  ext r
  simp only [kw_no3a_wdp_mprt_aqcCR_zAP, RingHom.comp_apply, zChartAwayDehom_const]
  rfl

end WeierstrassProjModel

end

end MEGA_KwNo3aWdpMprtZBridgeCRDischarge_lean
p2m_open "MvPolynomial HomogeneousLocalization HomogeneousIdealQuotientGrading WeierstrassProjModel P2MW.S_WeierstrassProjModel_exists_zChartAway_equiv_coordinateRing.WeierstrassProjModel P2MW.S_WeierstrassProjModel_exists_zChartAway_equiv_coordinateRing.ProjWeierstrassDehomog"

section BridgeEngine

variable {R : Type u} [CommRing R]

attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 32000000 in

theorem kw_brz_bridge_of_ambientPresent (V : WeierstrassCurve.Projective R)
    (i : Fin 3) {T : Type u} [CommRing T]
    (g : HomogeneousLocalization.Away (homogeneousSubmodule (Fin 3) R)
        (X i : MvPolynomial (Fin 3) R) →+* T)
    (alg : R →+* T)
    (hg_surj : Function.Surjective g)
    (hg_ker : RingHom.ker g = Ideal.span {kw_no3a_wdp_mprt_aqcCR_W_loc V i})
    (hg_compat : g.comp (kw_no3a_wdp_mprt_aqcCR_ambientFromR V i) = alg) :
    ∃ f : HomogeneousLocalization.Away (projModelGradingCR V)
            (Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal
              (X i : MvPolynomial (Fin 3) R)) →+* T,
      Function.Bijective f
      ∧ f.comp (kw_no3a_wdp_mprt_zcdCR_fromR V i) = alg
      ∧ ∀ (n : ℕ) (b : MvPolynomial (Fin 3) R)
          (hb : b ∈ homogeneousSubmodule (Fin 3) R (n • 1)),
          f (HomogeneousLocalization.Away.mk (projModelGradingCR V)
              (kw_no3a_wdp_mprt_aqcCR_mkX_mem_one V i) n
              (Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal b)
              (mk_mem_quotGradingSubmodule _ _ hb))
            = g (HomogeneousLocalization.Away.mk (homogeneousSubmodule (Fin 3) R)
                (X_mem_homogeneousSubmodule_one R i) n b hb) := by
  have hkeq : RingHom.ker (kw_no3a_wdp_mprt_aqcCR_q V i) = RingHom.ker g := by
    rw [kw_no3a_wdp_mprt_aqcCR_ker_q_eq_span, hg_ker]
  refine ⟨kw_no3a_wdp_mprt_aqcCR_liftOfSurjective (kw_no3a_wdp_mprt_aqcCR_q V i)
      (kw_no3a_wdp_mprt_aqcCR_q_surjective V i) g (le_of_eq hkeq),
    kw_no3a_wdp_mprt_aqcCR_liftOfSurjective_bijective _ _ _ hg_surj hkeq, ?_, ?_⟩
  · rw [← kw_no3a_wdp_mprt_aqcCR_q_comp_ambientFromR V i, ← RingHom.comp_assoc,
      kw_no3a_wdp_mprt_aqcCR_liftOfSurjective_comp, hg_compat]
  · intro n b hb
    rw [← kw_no3a_wdp_mprt_aqcCR_q_awayMk V i n b hb,
      kw_no3a_wdp_mprt_aqcCR_liftOfSurjective_apply]

end BridgeEngine

set_option maxHeartbeats 80000000 in
attribute [local instance] MvPolynomial.gradedAlgebra in

theorem solution
    {R : Type u} [CommRing R] (V : WeierstrassCurve.Projective R) :
    ∃ f : HomogeneousLocalization.Away (WeierstrassProjModel.projModelGradingCR V)
          (Ideal.Quotient.mk (WeierstrassProjModel.projModelHomogeneousIdealCR V).toIdeal
            (MvPolynomial.X 2 : MvPolynomial (Fin 3) R)) →+*
        (Polynomial (Polynomial R) ⧸ Ideal.span {V.toAffine.polynomial}),
      Function.Bijective f ∧
      f.comp ((HomogeneousLocalization.fromZeroRingHom (WeierstrassProjModel.projModelGradingCR V)
            (Submonoid.powers (Ideal.Quotient.mk
              (WeierstrassProjModel.projModelHomogeneousIdealCR V).toIdeal
              (MvPolynomial.X 2 : MvPolynomial (Fin 3) R)))).comp
          (algebraMap R (WeierstrassProjModel.projModelGradingCR V 0)))
        = algebraMap R (Polynomial (Polynomial R) ⧸ Ideal.span {V.toAffine.polynomial}) ∧
      ∀ (n : ℕ) (b : MvPolynomial (Fin 3) R)
        (hb : b ∈ MvPolynomial.homogeneousSubmodule (Fin 3) R (n • 1)),
        f (HomogeneousLocalization.Away.mk (WeierstrassProjModel.projModelGradingCR V)
            (HomogeneousIdealQuotientGrading.mk_mem_quotGradingSubmodule _ _
              ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr (MvPolynomial.isHomogeneous_X R 2)))
            n
            (Ideal.Quotient.mk (WeierstrassProjModel.projModelHomogeneousIdealCR V).toIdeal b)
            (HomogeneousIdealQuotientGrading.mk_mem_quotGradingSubmodule _ _ hb))
          = Ideal.Quotient.mk _
              (MvPolynomial.aeval
                (![Polynomial.C Polynomial.X, Polynomial.X, 1] : Fin 3 → Polynomial (Polynomial R)) b) := by
  obtain ⟨f, hbij, hcomp, hgen⟩ :=
    kw_brz_bridge_of_ambientPresent V 2 (kw_no3a_wdp_mprt_aqcCR_zAP V)
      (algebraMap R (Polynomial (Polynomial R) ⧸ Ideal.span {V.toAffine.polynomial}))
      (kw_no3a_wdp_mprt_aqcCR_zAP_surjective V) (kw_no3a_wdp_mprt_aqcCR_ker_zAP V)
      (kw_no3a_wdp_mprt_aqcCR_zAP_comp_ambientFromR V)
  refine ⟨f, hbij, hcomp, fun n b hb => (hgen n b hb).trans ?_⟩
  show Ideal.Quotient.mk _ (zChartAwayDehom R _) = _
  rw [zChartAwayDehom_awayMk]
  rfl

end S_WeierstrassProjModel_exists_zChartAway_equiv_coordinateRing
end P2MW
export P2MW.S_WeierstrassProjModel_exists_zChartAway_equiv_coordinateRing (solution)
