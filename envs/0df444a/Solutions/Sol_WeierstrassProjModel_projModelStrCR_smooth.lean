-- Prove2me | solution 1 for WeierstrassProjModel.projModelStrCR_smooth
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/8f5b0330-16d5-5c15-b14f-90f5c6c78546

import Definitions.Def_WeierstrassCurve_ProjModel
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.RingTheory.RingHom.Smooth
import Mathlib.RingTheory.RingHom.LocallyStandardSmooth
import Mathlib.RingTheory.Smooth.StandardSmooth
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic
import Theorems.Thm_WeierstrassProjModel_exists_ringEquiv_zChartAwayDegreeZero
import Theorems.Thm_WeierstrassProjModel_projModelStrCR_smooth_of_zChartBridge_of_yChartSmooth
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassProjModel_projModelStrCR_smooth

set_option autoImplicit false
set_option Elab.async false

namespace ProjWeierstrassDehomog

open MvPolynomial

section PointDictionary

variable {R : Type*} [CommRing R]

private theorem X_eq_zero_and_Y_ne_zero_of_Z_eq_zero [NoZeroDivisors R]
    {V : WeierstrassCurve.Projective R} {P : Fin 3 → R}
    (hP : eval P V.polynomial = 0) (hPz : P 2 = 0) (hP0 : P ≠ 0) :
    P 0 = 0 ∧ P 1 ≠ 0 := by
  have hx : P 0 = 0 := WeierstrassCurve.Projective.X_eq_zero_of_Z_eq_zero (W' := V) hP hPz
  refine ⟨hx, fun hy => hP0 ?_⟩
  funext i
  fin_cases i
  · exact hx
  · exact hy
  · exact hPz

end PointDictionary

variable {R : Type*} [CommRing R]

private theorem eval_polynomialZ_of_Z_eq_zero (V : WeierstrassCurve.Projective R) (P : Fin 3 → R)
    (hPz : P 2 = 0) :
    eval P V.polynomialZ = P 1 ^ 2 + V.a₁ * P 0 * P 1 - V.a₂ * P 0 ^ 2 := by
  rw [WeierstrassCurve.Projective.eval_polynomialZ, hPz]
  ring

private theorem nonsingular_of_equation_of_Z_eq_zero [NoZeroDivisors R]
    {V : WeierstrassCurve.Projective R} {P : Fin 3 → R}
    (hP : eval P V.polynomial = 0) (hPz : P 2 = 0) (hP0 : P ≠ 0) :
    V.Nonsingular P := by
  obtain ⟨hx, hy⟩ := X_eq_zero_and_Y_ne_zero_of_Z_eq_zero hP hPz hP0
  have hZ : eval P V.polynomialZ = P 1 ^ 2 := by
    rw [eval_polynomialZ_of_Z_eq_zero V P hPz, hx]
    ring
  refine ⟨hP, Or.inr (Or.inr ?_)⟩
  rw [hZ]
  exact pow_ne_zero 2 hy

private theorem nonsingular_of_equation_of_forall_affine_nonsingular {F : Type*} [Field F]
    {V : WeierstrassCurve.Projective F}
    (h : ∀ a b : F, V.toAffine.Equation a b → V.toAffine.Nonsingular a b)
    {P : Fin 3 → F} (hP : eval P V.polynomial = 0) (hP0 : P ≠ 0) :
    V.Nonsingular P := by
  by_cases hPz : P 2 = 0
  · exact nonsingular_of_equation_of_Z_eq_zero hP hPz hP0
  · have hE : V.Equation P := hP
    rw [WeierstrassCurve.Projective.nonsingular_of_Z_ne_zero hPz]
    exact h _ _ ((WeierstrassCurve.Projective.equation_of_Z_ne_zero hPz).mp hE)

private theorem nonsingular_of_equation_of_ne_zero_of_Δ_ne_zero {F : Type*} [Field F]
    {V : WeierstrassCurve.Projective F} (hΔ : V.Δ ≠ 0)
    {P : Fin 3 → F} (hP : V.Equation P) (hP0 : P ≠ 0) :
    V.Nonsingular P :=
  nonsingular_of_equation_of_forall_affine_nonsingular
    (fun _ _ hab => (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero hΔ).mp hab)
    hP hP0

private theorem nonsingular_of_equation_of_ne_zero {F : Type*} [Field F]
    {V : WeierstrassCurve.Projective F} [V.IsElliptic]
    {P : Fin 3 → F} (hP : V.Equation P) (hP0 : P ≠ 0) :
    V.Nonsingular P :=
  nonsingular_of_equation_of_ne_zero_of_Δ_ne_zero (WeierstrassCurve.isUnit_Δ V).ne_zero hP hP0

end ProjWeierstrassDehomog

noncomputable section

open MvPolynomial

namespace ProjWeierstrassDehomog

attribute [local instance] MvPolynomial.gradedAlgebra

section GradedPrelim

variable {R : Type*} [CommRing R]

variable (R) in

private theorem X_mem_homogeneousSubmodule_one (i : Fin 3) :
    (X i : MvPolynomial (Fin 3) R) ∈ homogeneousSubmodule (Fin 3) R 1 :=
  (mem_homogeneousSubmodule _ _).mpr (isHomogeneous_X _ i)

variable (R) in

private theorem C_mem_homogeneousSubmodule_zero (r : R) :
    (C r : MvPolynomial (Fin 3) R) ∈ homogeneousSubmodule (Fin 3) R 0 :=
  (mem_homogeneousSubmodule _ _).mpr (isHomogeneous_C _ _)

variable (R) in

private theorem one_mem_homogeneousSubmodule_zero :
    (1 : MvPolynomial (Fin 3) R) ∈ homogeneousSubmodule (Fin 3) R 0 :=
  (mem_homogeneousSubmodule _ _).mpr (isHomogeneous_one _ _)

end GradedPrelim

section Monomial

variable {R : Type*} [CommRing R]

private theorem monomial_eq_C_mul_pow (d : Fin 3 →₀ ℕ) (c : R) :
    (monomial d c : MvPolynomial (Fin 3) R)
      = C c * (X 0 ^ d 0 * X 1 ^ d 1 * X 2 ^ d 2) := by
  rw [MvPolynomial.monomial_eq, Finsupp.prod_fintype _ _ fun i => pow_zero _,
    Fin.prod_univ_three]

end Monomial

end ProjWeierstrassDehomog

end

noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousIdealQuotientGrading
open ProjWeierstrassCubicPrime HomogeneousLocalization

namespace WeierstrassProjModel
p2m_export "WeierstrassProjModel" "projModelHomogeneousIdealCR projModelHomogeneousIdealCR_toIdeal projModelGradingCR projModelStrCR exists_ringEquiv_zChartAwayDegreeZero projModelStrCR_smooth_of_zChartBridge_of_yChartSmooth"
p2m_open "WeierstrassProjModel"

attribute [local instance] MvPolynomial.gradedAlgebra

variable {R : Type} [CommRing R]

private def kw_no3a_wdp_mprt_zcdCR_fromR (V : WeierstrassCurve.Projective R) (i : Fin 3) :
    R →+* HomogeneousLocalization.Away (projModelGradingCR V)
      (Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal
        (X i : MvPolynomial (Fin 3) R)) :=
  (HomogeneousLocalization.fromZeroRingHom (projModelGradingCR V)
      (Submonoid.powers (Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal
        (X i : MvPolynomial (Fin 3) R)))).comp
    (algebraMap R ((projModelGradingCR V) 0))

private abbrev KwNo3aWdpMprtZChartAwayAffineCoordRingBridgeCR
    (V : WeierstrassCurve.Projective R) : Prop :=
  ∃ f : (HomogeneousLocalization.Away (projModelGradingCR V)
          (Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal
            (X 2 : MvPolynomial (Fin 3) R)))
        →+* (Polynomial (Polynomial R) ⧸ Ideal.span {V.toAffine.polynomial}),
    Function.Bijective f
    ∧ f.comp (kw_no3a_wdp_mprt_zcdCR_fromR V 2)
        = algebraMap R (Polynomial (Polynomial R) ⧸ Ideal.span {V.toAffine.polynomial})

private abbrev KwNo3aWdpMprtYChartFromRSmoothCR (V : WeierstrassCurve.Projective R) : Prop :=
  RingHom.Smooth (kw_no3a_wdp_mprt_zcdCR_fromR V 1)

end WeierstrassProjModel

end

noncomputable section

set_option maxHeartbeats 32000000
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousIdealQuotientGrading
open ProjWeierstrassCubicPrime ProjWeierstrassDehomog

namespace WeierstrassProjModel
p2m_export "WeierstrassProjModel" "projModelHomogeneousIdealCR projModelHomogeneousIdealCR_toIdeal projModelGradingCR projModelStrCR exists_ringEquiv_zChartAwayDegreeZero projModelStrCR_smooth_of_zChartBridge_of_yChartSmooth"
p2m_open "WeierstrassProjModel"

attribute [local instance] MvPolynomial.gradedAlgebra

variable {R : Type} [CommRing R]

private def kw_no3a_wdp_mprt_aqcCR_quotGradedRingHom (V : WeierstrassCurve.Projective R) :
    (homogeneousSubmodule (Fin 3) R) →+*ᵍ (projModelGradingCR V) where
  toRingHom := Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal
  map_mem ha := mk_mem_quotGradingSubmodule _ _ ha

private def kw_no3a_wdp_mprt_aqcCR_q (V : WeierstrassCurve.Projective R) (i : Fin 3) :
    HomogeneousLocalization.Away (homogeneousSubmodule (Fin 3) R)
        (X i : MvPolynomial (Fin 3) R) →+*
      HomogeneousLocalization.Away (projModelGradingCR V)
        (Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal
          (X i : MvPolynomial (Fin 3) R)) :=
  HomogeneousLocalization.Away.map (kw_no3a_wdp_mprt_aqcCR_quotGradedRingHom V) (X i)

private theorem kw_no3a_wdp_mprt_aqcCR_mkX_mem_one (V : WeierstrassCurve.Projective R) (i : Fin 3) :
    Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal (X i : MvPolynomial (Fin 3) R)
      ∈ projModelGradingCR V 1 :=
  mk_mem_quotGradingSubmodule _ _ (X_mem_homogeneousSubmodule_one R i)

private theorem kw_no3a_wdp_mprt_aqcCR_q_awayMk (V : WeierstrassCurve.Projective R) (i : Fin 3)
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

private theorem kw_no3a_wdp_mprt_aqcCR_Vpoly_mem (V : WeierstrassCurve.Projective R) :
    V.polynomial ∈ homogeneousSubmodule (Fin 3) R (3 • 1) := by
  rw [smul_eq_mul, mul_one]
  exact (mem_homogeneousSubmodule _ _).mpr (isHomogeneous_polynomial V)

private def kw_no3a_wdp_mprt_aqcCR_W_loc (V : WeierstrassCurve.Projective R) (i : Fin 3) :
    HomogeneousLocalization.Away (homogeneousSubmodule (Fin 3) R)
      (X i : MvPolynomial (Fin 3) R) :=
  HomogeneousLocalization.Away.mk (homogeneousSubmodule (Fin 3) R)
    (X_mem_homogeneousSubmodule_one R i) 3 V.polynomial (kw_no3a_wdp_mprt_aqcCR_Vpoly_mem V)

private def kw_no3a_wdp_mprt_aqcCR_ambientFromRElem (i : Fin 3) (r : R) :
    HomogeneousLocalization.Away (homogeneousSubmodule (Fin 3) R)
      (X i : MvPolynomial (Fin 3) R) :=
  HomogeneousLocalization.mk
    ⟨0, ⟨C r, C_mem_homogeneousSubmodule_zero R r⟩, ⟨1, one_mem_homogeneousSubmodule_zero R⟩,
      ⟨0, pow_zero _⟩⟩

private theorem kw_no3a_wdp_mprt_aqcCR_ambientFromRElem_val (i : Fin 3) (r : R) :
    (kw_no3a_wdp_mprt_aqcCR_ambientFromRElem i r).val
      = Localization.mk (C r : MvPolynomial (Fin 3) R)
          (1 : Submonoid.powers (X i : MvPolynomial (Fin 3) R)) :=
  rfl

private def kw_no3a_wdp_mprt_aqcCR_ambientFromR (_V : WeierstrassCurve.Projective R) (i : Fin 3) :
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

private theorem kw_no3a_wdp_mprt_aqcCR_ambientFromR_val (V : WeierstrassCurve.Projective R)
    (i : Fin 3) (r : R) :
    (kw_no3a_wdp_mprt_aqcCR_ambientFromR V i r).val
      = Localization.mk (C r : MvPolynomial (Fin 3) R)
          (1 : Submonoid.powers (X i : MvPolynomial (Fin 3) R)) :=
  rfl

private noncomputable def kw_no3a_wdp_mprt_aqcCR_liftOfSurjective {A B C : Type*} [CommRing A]
    [CommRing B] [CommRing C] (f : A →+* B) (hf : Function.Surjective f) (g : A →+* C)
    (H : RingHom.ker f ≤ RingHom.ker g) : B →+* C :=
  (Ideal.Quotient.lift _ g (fun _ ha => RingHom.mem_ker.mp (H ha))).comp
    (RingHom.quotientKerEquivOfSurjective hf).symm.toRingHom

private theorem kw_no3a_wdp_mprt_aqcCR_liftOfSurjective_comp {A B C : Type*} [CommRing A] [CommRing B]
    [CommRing C] (f : A →+* B) (hf : Function.Surjective f) (g : A →+* C)
    (H : RingHom.ker f ≤ RingHom.ker g) :
    (kw_no3a_wdp_mprt_aqcCR_liftOfSurjective f hf g H).comp f = g := by
  unfold kw_no3a_wdp_mprt_aqcCR_liftOfSurjective
  rw [RingHom.comp_assoc, RingHom.quotientKerEquivOfSurjective_symm_comp]
  exact Ideal.Quotient.lift_comp_mk _ _ _

private theorem kw_no3a_wdp_mprt_aqcCR_liftOfSurjective_apply {A B C : Type*} [CommRing A] [CommRing B]
    [CommRing C] (f : A →+* B) (hf : Function.Surjective f) (g : A →+* C)
    (H : RingHom.ker f ≤ RingHom.ker g) (a : A) :
    kw_no3a_wdp_mprt_aqcCR_liftOfSurjective f hf g H (f a) = g a :=
  RingHom.congr_fun (kw_no3a_wdp_mprt_aqcCR_liftOfSurjective_comp f hf g H) a

private theorem kw_no3a_wdp_mprt_aqcCR_liftOfSurjective_bijective {A B C : Type*} [CommRing A]
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

private theorem kw_no3a_wdp_mprt_aqcCR_q_surjective (V : WeierstrassCurve.Projective R) (i : Fin 3) :
    Function.Surjective (kw_no3a_wdp_mprt_aqcCR_q V i) := by
  intro y
  obtain ⟨n, a, ha, rfl⟩ :=
    HomogeneousLocalization.Away.mk_surjective (projModelGradingCR V)
      (kw_no3a_wdp_mprt_aqcCR_mkX_mem_one V i) y
  obtain ⟨b, hb, rfl⟩ := (mem_quotGradingSubmodule_iff _ _).mp ha
  exact ⟨HomogeneousLocalization.Away.mk (homogeneousSubmodule (Fin 3) R)
    (X_mem_homogeneousSubmodule_one R i) n b hb, kw_no3a_wdp_mprt_aqcCR_q_awayMk V i n b hb⟩

private theorem kw_no3a_wdp_mprt_aqcCR_q_W_loc_eq_zero (V : WeierstrassCurve.Projective R)
    (i : Fin 3) :
    kw_no3a_wdp_mprt_aqcCR_q V i (kw_no3a_wdp_mprt_aqcCR_W_loc V i) = 0 := by
  have hzero : Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal V.polynomial = 0 := by
    rw [Ideal.Quotient.eq_zero_iff_mem, projModelHomogeneousIdealCR_toIdeal]
    exact Ideal.mem_span_singleton_self _
  rw [kw_no3a_wdp_mprt_aqcCR_W_loc, kw_no3a_wdp_mprt_aqcCR_q_awayMk,
    HomogeneousLocalization.ext_iff_val, HomogeneousLocalization.val_zero,
    HomogeneousLocalization.Away.val_mk, hzero, Localization.mk_zero]

private theorem kw_no3a_wdp_mprt_aqcCR_homogeneousCofactor (V : WeierstrassCurve.Projective R)
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

private theorem kw_no3a_wdp_mprt_aqcCR_ker_q_le_span (V : WeierstrassCurve.Projective R) (i : Fin 3) :
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

private theorem kw_no3a_wdp_mprt_aqcCR_ker_q_eq_span (V : WeierstrassCurve.Projective R) (i : Fin 3) :
    RingHom.ker (kw_no3a_wdp_mprt_aqcCR_q V i)
      = Ideal.span {kw_no3a_wdp_mprt_aqcCR_W_loc V i} :=
  le_antisymm (kw_no3a_wdp_mprt_aqcCR_ker_q_le_span V i)
    (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr
      (RingHom.mem_ker.mpr (kw_no3a_wdp_mprt_aqcCR_q_W_loc_eq_zero V i))))

private theorem kw_no3a_wdp_mprt_aqcCR_fromR_val (V : WeierstrassCurve.Projective R) (i : Fin 3)
    (r : R) :
    (kw_no3a_wdp_mprt_zcdCR_fromR V i r).val
      = Localization.mk (Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal (C r))
          (1 : Submonoid.powers (Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal
            (X i : MvPolynomial (Fin 3) R))) :=
  rfl

private theorem kw_no3a_wdp_mprt_aqcCR_q_comp_ambientFromR (V : WeierstrassCurve.Projective R)
    (i : Fin 3) :
    (kw_no3a_wdp_mprt_aqcCR_q V i).comp (kw_no3a_wdp_mprt_aqcCR_ambientFromR V i)
      = kw_no3a_wdp_mprt_zcdCR_fromR V i := by
  refine RingHom.ext fun r => ?_
  rw [HomogeneousLocalization.ext_iff_val, kw_no3a_wdp_mprt_aqcCR_fromR_val, RingHom.comp_apply]
  simp only [kw_no3a_wdp_mprt_aqcCR_q, kw_no3a_wdp_mprt_aqcCR_ambientFromR, RingHom.coe_mk,
    MonoidHom.coe_mk, OneHom.coe_mk, kw_no3a_wdp_mprt_aqcCR_ambientFromRElem,
    HomogeneousLocalization.Away.map]
  rfl

set_option maxHeartbeats 32000000 in

private theorem kw_no3a_wdp_mprt_aqcCR_bridge_of_ambientPresent (V : WeierstrassCurve.Projective R)
    (i : Fin 3) {T : Type} [CommRing T]
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
      ∧ f.comp (kw_no3a_wdp_mprt_zcdCR_fromR V i) = alg := by
  have hkeq : RingHom.ker (kw_no3a_wdp_mprt_aqcCR_q V i) = RingHom.ker g := by
    rw [kw_no3a_wdp_mprt_aqcCR_ker_q_eq_span, hg_ker]
  refine ⟨kw_no3a_wdp_mprt_aqcCR_liftOfSurjective (kw_no3a_wdp_mprt_aqcCR_q V i)
      (kw_no3a_wdp_mprt_aqcCR_q_surjective V i) g (le_of_eq hkeq),
    kw_no3a_wdp_mprt_aqcCR_liftOfSurjective_bijective _ _ _ hg_surj hkeq, ?_⟩
  rw [← kw_no3a_wdp_mprt_aqcCR_q_comp_ambientFromR V i, ← RingHom.comp_assoc,
    kw_no3a_wdp_mprt_aqcCR_liftOfSurjective_comp, hg_compat]

section ZAP

variable (e : HomogeneousLocalization.Away (homogeneousSubmodule (Fin 3) R)
      (X 2 : MvPolynomial (Fin 3) R) ≃+* Polynomial (Polynomial R))

private theorem kw_no3a_wdp_mprt_aqcCR_ambientFromRElem_eq_awayMk (i : Fin 3) (r : R) :
    kw_no3a_wdp_mprt_aqcCR_ambientFromRElem i r
      = HomogeneousLocalization.Away.mk (homogeneousSubmodule (Fin 3) R)
          ((mem_homogeneousSubmodule _ _).mpr (isHomogeneous_X _ i)) 0 (C r)
          (by rw [zero_nsmul]; exact C_mem_homogeneousSubmodule_zero R r) := by
  apply HomogeneousLocalization.val_injective
  rw [kw_no3a_wdp_mprt_aqcCR_ambientFromRElem_val, HomogeneousLocalization.Away.val_mk]
  exact congrArg (Localization.mk (C r : MvPolynomial (Fin 3) R)) (Subtype.ext (pow_zero _).symm)

private def kw_no3a_wdp_mprt_aqcCR_zAP (V : WeierstrassCurve.Projective R) :
    HomogeneousLocalization.Away (homogeneousSubmodule (Fin 3) R)
        (X 2 : MvPolynomial (Fin 3) R) →+*
      (Polynomial (Polynomial R) ⧸ Ideal.span {V.toAffine.polynomial}) :=
  (Ideal.Quotient.mk (Ideal.span {V.toAffine.polynomial})).comp e.toRingHom

private theorem kw_no3a_wdp_mprt_aqcCR_zAP_apply (V : WeierstrassCurve.Projective R)
    (z : HomogeneousLocalization.Away (homogeneousSubmodule (Fin 3) R) (X 2 : MvPolynomial (Fin 3) R)) :
    kw_no3a_wdp_mprt_aqcCR_zAP e V z = Ideal.Quotient.mk (Ideal.span {V.toAffine.polynomial}) (e z) :=
  rfl

private theorem kw_no3a_wdp_mprt_aqcCR_zAP_surjective (V : WeierstrassCurve.Projective R) :
    Function.Surjective (kw_no3a_wdp_mprt_aqcCR_zAP e V) := by
  intro y
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective y
  exact ⟨e.symm p, by rw [kw_no3a_wdp_mprt_aqcCR_zAP_apply, RingEquiv.apply_symm_apply]⟩

variable (he : ∀ (n : ℕ) (a : MvPolynomial (Fin 3) R)
        (ha : a ∈ homogeneousSubmodule (Fin 3) R (n • 1)),
        e (HomogeneousLocalization.Away.mk (homogeneousSubmodule (Fin 3) R)
            ((mem_homogeneousSubmodule _ _).mpr (isHomogeneous_X _ 2)) n a ha)
          = aeval (![Polynomial.C Polynomial.X, Polynomial.X, 1] :
              Fin 3 → Polynomial (Polynomial R)) a)
include he

private theorem kw_no3a_wdp_mprt_aqcCR_e_W_loc (V : WeierstrassCurve.Projective R)
    (hW : aeval (![Polynomial.C Polynomial.X, Polynomial.X, 1] :
          Fin 3 → Polynomial (Polynomial R)) V.polynomial = V.toAffine.polynomial) :
    e (kw_no3a_wdp_mprt_aqcCR_W_loc V 2) = V.toAffine.polynomial := by
  unfold kw_no3a_wdp_mprt_aqcCR_W_loc
  rw [he]
  exact hW

private theorem kw_no3a_wdp_mprt_aqcCR_ker_zAP (V : WeierstrassCurve.Projective R)
    (hW : aeval (![Polynomial.C Polynomial.X, Polynomial.X, 1] :
          Fin 3 → Polynomial (Polynomial R)) V.polynomial = V.toAffine.polynomial) :
    RingHom.ker (kw_no3a_wdp_mprt_aqcCR_zAP e V)
      = Ideal.span {kw_no3a_wdp_mprt_aqcCR_W_loc V 2} := by
  have hWl := kw_no3a_wdp_mprt_aqcCR_e_W_loc e he V hW
  refine le_antisymm ?_ (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (RingHom.mem_ker.mpr ?_)))
  · intro x hx
    rw [RingHom.mem_ker, kw_no3a_wdp_mprt_aqcCR_zAP_apply, Ideal.Quotient.eq_zero_iff_mem,
      Ideal.mem_span_singleton'] at hx
    obtain ⟨q, hq⟩ := hx
    refine Ideal.mem_span_singleton'.mpr ⟨e.symm q, ?_⟩
    apply e.injective
    rw [map_mul, RingEquiv.apply_symm_apply, hWl, hq]
  · rw [kw_no3a_wdp_mprt_aqcCR_zAP_apply, hWl, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_span_singleton_self _

private theorem kw_no3a_wdp_mprt_aqcCR_zAP_comp_ambientFromR (V : WeierstrassCurve.Projective R) :
    (kw_no3a_wdp_mprt_aqcCR_zAP e V).comp (kw_no3a_wdp_mprt_aqcCR_ambientFromR V 2)
      = algebraMap R (Polynomial (Polynomial R) ⧸ Ideal.span {V.toAffine.polynomial}) := by
  refine RingHom.ext fun r => ?_
  show Ideal.Quotient.mk (Ideal.span {V.toAffine.polynomial})
      (e (kw_no3a_wdp_mprt_aqcCR_ambientFromRElem 2 r)) = _
  rw [kw_no3a_wdp_mprt_aqcCR_ambientFromRElem_eq_awayMk, he, MvPolynomial.aeval_C]
  rfl

end ZAP

set_option maxHeartbeats 80000000 in

private theorem kw_no3a_wdp_mprt_aqcCR_zBridge_holds (V : WeierstrassCurve.Projective R) :
    KwNo3aWdpMprtZChartAwayAffineCoordRingBridgeCR V := by
  obtain ⟨⟨e, he⟩, hW⟩ := exists_ringEquiv_zChartAwayDegreeZero R
  exact kw_no3a_wdp_mprt_aqcCR_bridge_of_ambientPresent V 2 (kw_no3a_wdp_mprt_aqcCR_zAP e V)
    (algebraMap R (Polynomial (Polynomial R) ⧸ Ideal.span {V.toAffine.polynomial}))
    (kw_no3a_wdp_mprt_aqcCR_zAP_surjective e V) (kw_no3a_wdp_mprt_aqcCR_ker_zAP e he V (hW V))
    (kw_no3a_wdp_mprt_aqcCR_zAP_comp_ambientFromR e he V)

private theorem kw_no3a_wdp_mprt_aqcCR_smooth_projModelStrCR_of_yFromR
    (V : WeierstrassCurve.Projective R) [V.IsElliptic]
    (hy : KwNo3aWdpMprtYChartFromRSmoothCR V) :
    Smooth (projModelStrCR V) :=
  projModelStrCR_smooth_of_zChartBridge_of_yChartSmooth V
    (kw_no3a_wdp_mprt_aqcCR_zBridge_holds V) hy

end WeierstrassProjModel

end

noncomputable section

set_option maxHeartbeats 6400000
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousIdealQuotientGrading
open ProjWeierstrassCubicPrime ProjWeierstrassDehomog

namespace WeierstrassProjModel
p2m_export "WeierstrassProjModel" "projModelHomogeneousIdealCR projModelHomogeneousIdealCR_toIdeal projModelGradingCR projModelStrCR exists_ringEquiv_zChartAwayDegreeZero projModelStrCR_smooth_of_zChartBridge_of_yChartSmooth"
p2m_open "WeierstrassProjModel"

attribute [local instance] MvPolynomial.gradedAlgebra

variable {R : Type} [CommRing R]

private theorem kw_no3a_wdp_mprt_ydeCR_algHom_C {L : Type*} [CommRing L] [Algebra R L]
    (π : MvPolynomial (Fin 2) R →ₐ[R] L) (r : R) :
    π (MvPolynomial.C r) = algebraMap R L r := by
  rw [← MvPolynomial.algebraMap_eq]; exact π.commutes r

private noncomputable def kw_no3a_wdp_mprt_ydeCR_W_Y (V : WeierstrassCurve.Projective R) :
    MvPolynomial (Fin 2) R :=
  MvPolynomial.X 1
    + MvPolynomial.C V.a₁ * MvPolynomial.X 0 * MvPolynomial.X 1
    + MvPolynomial.C V.a₃ * (MvPolynomial.X 1) ^ 2
    - ((MvPolynomial.X 0) ^ 3
        + MvPolynomial.C V.a₂ * (MvPolynomial.X 0) ^ 2 * MvPolynomial.X 1
        + MvPolynomial.C V.a₄ * MvPolynomial.X 0 * (MvPolynomial.X 1) ^ 2
        + MvPolynomial.C V.a₆ * (MvPolynomial.X 1) ^ 3)

private abbrev kw_no3a_wdp_mprt_ydeCR_coordRing (V : WeierstrassCurve.Projective R) : Type :=
  MvPolynomial (Fin 2) R
    ⧸ Ideal.span (Set.range (fun _ : Fin 1 => kw_no3a_wdp_mprt_ydeCR_W_Y V))

private def kw_no3a_wdp_mprt_ydeCR_mkYPartial (V : WeierstrassCurve.Projective R) (j : Fin 2) :
    kw_no3a_wdp_mprt_ydeCR_coordRing V :=
  Ideal.Quotient.mk _ (MvPolynomial.pderiv j (kw_no3a_wdp_mprt_ydeCR_W_Y V))

private theorem kw_no3a_wdp_mprt_ydeCR_algHom_W_Y {L : Type*} [CommRing L] [Algebra R L]
    (π : MvPolynomial (Fin 2) R →ₐ[R] L) (V : WeierstrassCurve.Projective R) :
    π (kw_no3a_wdp_mprt_ydeCR_W_Y V)
      = MvPolynomial.eval
          ![π (MvPolynomial.X 0), 1, π (MvPolynomial.X 1)]
          (V.map (algebraMap R L)).polynomial := by
  rw [WeierstrassCurve.Projective.eval_polynomial]
  simp only [kw_no3a_wdp_mprt_ydeCR_W_Y, map_sub, map_add, map_mul, map_pow,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons,
    WeierstrassCurve.map, kw_no3a_wdp_mprt_ydeCR_algHom_C]
  ring

private noncomputable def kw_no3a_wdp_mprt_ydeCR_dehomY :
    MvPolynomial (Fin 3) R →ₐ[R] MvPolynomial (Fin 2) R :=
  MvPolynomial.aeval ![MvPolynomial.X 0, 1, MvPolynomial.X 1]

private theorem kw_no3a_wdp_mprt_ydeCR_dehomY_X_zero :
    kw_no3a_wdp_mprt_ydeCR_dehomY (X 0 : MvPolynomial (Fin 3) R) = MvPolynomial.X 0 := by
  simp [kw_no3a_wdp_mprt_ydeCR_dehomY]

private theorem kw_no3a_wdp_mprt_ydeCR_dehomY_X_one :
    kw_no3a_wdp_mprt_ydeCR_dehomY (X 1 : MvPolynomial (Fin 3) R)
      = (1 : MvPolynomial (Fin 2) R) := by
  simp [kw_no3a_wdp_mprt_ydeCR_dehomY]

private theorem kw_no3a_wdp_mprt_ydeCR_dehomY_X_two :
    kw_no3a_wdp_mprt_ydeCR_dehomY (X 2 : MvPolynomial (Fin 3) R) = MvPolynomial.X 1 := by
  simp [kw_no3a_wdp_mprt_ydeCR_dehomY]

private theorem kw_no3a_wdp_mprt_ydeCR_dehomY_C (r : R) :
    kw_no3a_wdp_mprt_ydeCR_dehomY (C r : MvPolynomial (Fin 3) R) = MvPolynomial.C r := by
  simp [kw_no3a_wdp_mprt_ydeCR_dehomY]

private def kw_no3a_wdp_mprt_ydeCR_yX :
    HomogeneousLocalization.Away (homogeneousSubmodule (Fin 3) R)
      (X 1 : MvPolynomial (Fin 3) R) :=
  HomogeneousLocalization.mk
    ⟨1, ⟨X 0, X_mem_homogeneousSubmodule_one R 0⟩, ⟨X 1, X_mem_homogeneousSubmodule_one R 1⟩,
      ⟨1, pow_one _⟩⟩

private theorem kw_no3a_wdp_mprt_ydeCR_yX_val :
    (kw_no3a_wdp_mprt_ydeCR_yX (R := R)).val
      = Localization.mk (X 0 : MvPolynomial (Fin 3) R)
          (⟨X 1, 1, pow_one _⟩ : Submonoid.powers (X 1 : MvPolynomial (Fin 3) R)) :=
  rfl

private def kw_no3a_wdp_mprt_ydeCR_yZ :
    HomogeneousLocalization.Away (homogeneousSubmodule (Fin 3) R)
      (X 1 : MvPolynomial (Fin 3) R) :=
  HomogeneousLocalization.mk
    ⟨1, ⟨X 2, X_mem_homogeneousSubmodule_one R 2⟩, ⟨X 1, X_mem_homogeneousSubmodule_one R 1⟩,
      ⟨1, pow_one _⟩⟩

private theorem kw_no3a_wdp_mprt_ydeCR_yZ_val :
    (kw_no3a_wdp_mprt_ydeCR_yZ (R := R)).val
      = Localization.mk (X 2 : MvPolynomial (Fin 3) R)
          (⟨X 1, 1, pow_one _⟩ : Submonoid.powers (X 1 : MvPolynomial (Fin 3) R)) :=
  rfl

private theorem kw_no3a_wdp_mprt_ydeCR_aeval_polynomial {S : Type*} [CommRing S] [Algebra R S]
    (V : WeierstrassCurve.Projective R) (f : Fin 3 → S) :
    MvPolynomial.aeval f V.polynomial
      = MvPolynomial.eval f (V.map (algebraMap R S)).polynomial := by
  rw [WeierstrassCurve.Projective.eval_polynomial, MvPolynomial.aeval_def,
    WeierstrassCurve.Projective.polynomial]
  simp only [eval₂_sub, eval₂_add, eval₂_mul, eval₂_pow, eval₂_X, eval₂_C,
    WeierstrassCurve.map]

private theorem kw_no3a_wdp_mprt_ydeCR_dehomY_polynomial (V : WeierstrassCurve.Projective R) :
    kw_no3a_wdp_mprt_ydeCR_dehomY V.polynomial = kw_no3a_wdp_mprt_ydeCR_W_Y V := by
  have h := kw_no3a_wdp_mprt_ydeCR_algHom_W_Y
    (AlgHom.id R (MvPolynomial (Fin 2) R)) V
  simp only [AlgHom.id_apply] at h
  rw [h, kw_no3a_wdp_mprt_ydeCR_dehomY]
  exact kw_no3a_wdp_mprt_ydeCR_aeval_polynomial V ![X 0, 1, X 1]

private theorem kw_no3a_wdp_mprt_ydeCR_dehomY_X_one_mul_one :
    (kw_no3a_wdp_mprt_ydeCR_dehomY (R := R)).toRingHom (X 1) * 1 = 1 := by
  show kw_no3a_wdp_mprt_ydeCR_dehomY (X 1 : MvPolynomial (Fin 3) R) * 1 = 1
  rw [kw_no3a_wdp_mprt_ydeCR_dehomY_X_one, mul_one]

private def kw_no3a_wdp_mprt_ydeCR_yLocDehom :
    Localization.Away (X 1 : MvPolynomial (Fin 3) R) →+* MvPolynomial (Fin 2) R :=
  Localization.awayLift (kw_no3a_wdp_mprt_ydeCR_dehomY (R := R)).toRingHom (X 1)
    (isUnit_iff_exists_inv.mpr ⟨1, kw_no3a_wdp_mprt_ydeCR_dehomY_X_one_mul_one⟩)

private theorem kw_no3a_wdp_mprt_ydeCR_yLocDehom_mk (a : MvPolynomial (Fin 3) R) (n : ℕ) :
    kw_no3a_wdp_mprt_ydeCR_yLocDehom
        (Localization.mk a
          (⟨X 1 ^ n, n, rfl⟩ : Submonoid.powers (X 1 : MvPolynomial (Fin 3) R)))
      = kw_no3a_wdp_mprt_ydeCR_dehomY a := by
  have h := Localization.awayLift_mk (A := MvPolynomial (Fin 2) R)
    (kw_no3a_wdp_mprt_ydeCR_dehomY (R := R)).toRingHom (X 1) a 1
    kw_no3a_wdp_mprt_ydeCR_dehomY_X_one_mul_one n
  rw [one_pow, mul_one] at h
  exact h

private def kw_no3a_wdp_mprt_ydeCR_yChartAwayDehom :
    HomogeneousLocalization.Away (homogeneousSubmodule (Fin 3) R)
        (X 1 : MvPolynomial (Fin 3) R) →+* MvPolynomial (Fin 2) R :=
  (kw_no3a_wdp_mprt_ydeCR_yLocDehom (R := R)).comp
    (algebraMap
      (HomogeneousLocalization.Away (homogeneousSubmodule (Fin 3) R)
        (X 1 : MvPolynomial (Fin 3) R))
      (Localization.Away (X 1 : MvPolynomial (Fin 3) R)))

private def kw_no3a_wdp_mprt_ydeCR_yToVal :
    HomogeneousLocalization.Away (homogeneousSubmodule (Fin 3) R)
        (X 1 : MvPolynomial (Fin 3) R) →+*
      Localization.Away (X 1 : MvPolynomial (Fin 3) R) :=
  algebraMap
    (HomogeneousLocalization.Away (homogeneousSubmodule (Fin 3) R)
      (X 1 : MvPolynomial (Fin 3) R))
    (Localization.Away (X 1 : MvPolynomial (Fin 3) R))

private theorem kw_no3a_wdp_mprt_ydeCR_yToVal_eq_val
    (z : HomogeneousLocalization.Away (homogeneousSubmodule (Fin 3) R)
      (X 1 : MvPolynomial (Fin 3) R)) :
    kw_no3a_wdp_mprt_ydeCR_yToVal (R := R) z = z.val :=
  HomogeneousLocalization.algebraMap_apply z

private theorem kw_no3a_wdp_mprt_ydeCR_yChartAwayDehom_awayMk (n : ℕ) (a : MvPolynomial (Fin 3) R)
    (ha : a ∈ homogeneousSubmodule (Fin 3) R (n • 1)) :
    kw_no3a_wdp_mprt_ydeCR_yChartAwayDehom (R := R)
        (HomogeneousLocalization.Away.mk (homogeneousSubmodule (Fin 3) R)
          (X_mem_homogeneousSubmodule_one R 1) n a ha)
      = kw_no3a_wdp_mprt_ydeCR_dehomY a := by
  show kw_no3a_wdp_mprt_ydeCR_yLocDehom
      (kw_no3a_wdp_mprt_ydeCR_yToVal (R := R)
        (HomogeneousLocalization.Away.mk (homogeneousSubmodule (Fin 3) R)
          (X_mem_homogeneousSubmodule_one R 1) n a ha))
    = kw_no3a_wdp_mprt_ydeCR_dehomY a
  rw [kw_no3a_wdp_mprt_ydeCR_yToVal_eq_val]
  have hval : (HomogeneousLocalization.Away.mk (homogeneousSubmodule (Fin 3) R)
        (X_mem_homogeneousSubmodule_one R 1) n a ha).val
      = Localization.mk a
          (⟨X 1 ^ n, n, rfl⟩ : Submonoid.powers (X 1 : MvPolynomial (Fin 3) R)) := rfl
  rw [hval, kw_no3a_wdp_mprt_ydeCR_yLocDehom_mk]

private theorem kw_no3a_wdp_mprt_ydeCR_yChartAwayDehom_yX :
    kw_no3a_wdp_mprt_ydeCR_yChartAwayDehom (R := R) kw_no3a_wdp_mprt_ydeCR_yX
      = MvPolynomial.X 0 := by
  show kw_no3a_wdp_mprt_ydeCR_yLocDehom
    (kw_no3a_wdp_mprt_ydeCR_yToVal (R := R) kw_no3a_wdp_mprt_ydeCR_yX) = _
  rw [kw_no3a_wdp_mprt_ydeCR_yToVal_eq_val, kw_no3a_wdp_mprt_ydeCR_yX_val]
  have h1 : (⟨(X 1 : MvPolynomial (Fin 3) R), 1, pow_one _⟩ :
        Submonoid.powers (X 1 : MvPolynomial (Fin 3) R))
      = ⟨X 1 ^ 1, 1, rfl⟩ := Subtype.ext (pow_one _).symm
  rw [h1, kw_no3a_wdp_mprt_ydeCR_yLocDehom_mk, kw_no3a_wdp_mprt_ydeCR_dehomY_X_zero]

private theorem kw_no3a_wdp_mprt_ydeCR_yChartAwayDehom_yZ :
    kw_no3a_wdp_mprt_ydeCR_yChartAwayDehom (R := R) kw_no3a_wdp_mprt_ydeCR_yZ
      = MvPolynomial.X 1 := by
  show kw_no3a_wdp_mprt_ydeCR_yLocDehom
    (kw_no3a_wdp_mprt_ydeCR_yToVal (R := R) kw_no3a_wdp_mprt_ydeCR_yZ) = _
  rw [kw_no3a_wdp_mprt_ydeCR_yToVal_eq_val, kw_no3a_wdp_mprt_ydeCR_yZ_val]
  have h1 : (⟨(X 1 : MvPolynomial (Fin 3) R), 1, pow_one _⟩ :
        Submonoid.powers (X 1 : MvPolynomial (Fin 3) R))
      = ⟨X 1 ^ 1, 1, rfl⟩ := Subtype.ext (pow_one _).symm
  rw [h1, kw_no3a_wdp_mprt_ydeCR_yLocDehom_mk, kw_no3a_wdp_mprt_ydeCR_dehomY_X_two]

private theorem kw_no3a_wdp_mprt_ydeCR_yChartAwayDehom_const (V : WeierstrassCurve.Projective R)
    (r : R) :
    kw_no3a_wdp_mprt_ydeCR_yChartAwayDehom (R := R)
        (kw_no3a_wdp_mprt_aqcCR_ambientFromR V 1 r)
      = MvPolynomial.C r := by
  show kw_no3a_wdp_mprt_ydeCR_yLocDehom
    (kw_no3a_wdp_mprt_ydeCR_yToVal (R := R) (kw_no3a_wdp_mprt_aqcCR_ambientFromR V 1 r)) = _
  rw [kw_no3a_wdp_mprt_ydeCR_yToVal_eq_val, kw_no3a_wdp_mprt_aqcCR_ambientFromR_val]
  have h1 : (1 : Submonoid.powers (X 1 : MvPolynomial (Fin 3) R)) = ⟨X 1 ^ 0, 0, rfl⟩ :=
    Subtype.ext (pow_zero _).symm
  rw [h1, kw_no3a_wdp_mprt_ydeCR_yLocDehom_mk, kw_no3a_wdp_mprt_ydeCR_dehomY_C]

private def kw_no3a_wdp_mprt_ydeCR_yHomog (V : WeierstrassCurve.Projective R) :
    MvPolynomial (Fin 2) R →+*
      HomogeneousLocalization.Away (homogeneousSubmodule (Fin 3) R)
        (X 1 : MvPolynomial (Fin 3) R) :=
  MvPolynomial.eval₂Hom (kw_no3a_wdp_mprt_aqcCR_ambientFromR V 1)
    ![kw_no3a_wdp_mprt_ydeCR_yX, kw_no3a_wdp_mprt_ydeCR_yZ]

private theorem kw_no3a_wdp_mprt_ydeCR_yHomog_X_zero (V : WeierstrassCurve.Projective R) :
    kw_no3a_wdp_mprt_ydeCR_yHomog V (MvPolynomial.X 0) = kw_no3a_wdp_mprt_ydeCR_yX := by
  simp [kw_no3a_wdp_mprt_ydeCR_yHomog]

private theorem kw_no3a_wdp_mprt_ydeCR_yHomog_X_one (V : WeierstrassCurve.Projective R) :
    kw_no3a_wdp_mprt_ydeCR_yHomog V (MvPolynomial.X 1) = kw_no3a_wdp_mprt_ydeCR_yZ := by
  simp [kw_no3a_wdp_mprt_ydeCR_yHomog]

private theorem kw_no3a_wdp_mprt_ydeCR_yHomog_C (V : WeierstrassCurve.Projective R) (r : R) :
    kw_no3a_wdp_mprt_ydeCR_yHomog V (MvPolynomial.C r)
      = kw_no3a_wdp_mprt_aqcCR_ambientFromR V 1 r := by
  simp [kw_no3a_wdp_mprt_ydeCR_yHomog]

private theorem kw_no3a_wdp_mprt_ydeCR_dehom_comp_homog (V : WeierstrassCurve.Projective R) :
    (kw_no3a_wdp_mprt_ydeCR_yChartAwayDehom (R := R)).comp
        (kw_no3a_wdp_mprt_ydeCR_yHomog V)
      = RingHom.id (MvPolynomial (Fin 2) R) := by
  refine MvPolynomial.ringHom_ext (fun r => ?_) (fun j => ?_)
  · rw [RingHom.comp_apply, kw_no3a_wdp_mprt_ydeCR_yHomog_C,
      kw_no3a_wdp_mprt_ydeCR_yChartAwayDehom_const, RingHom.id_apply]
  · fin_cases j
    · show kw_no3a_wdp_mprt_ydeCR_yChartAwayDehom (R := R)
          (kw_no3a_wdp_mprt_ydeCR_yHomog V (MvPolynomial.X 0)) = MvPolynomial.X 0
      rw [kw_no3a_wdp_mprt_ydeCR_yHomog_X_zero, kw_no3a_wdp_mprt_ydeCR_yChartAwayDehom_yX]
    · show kw_no3a_wdp_mprt_ydeCR_yChartAwayDehom (R := R)
          (kw_no3a_wdp_mprt_ydeCR_yHomog V (MvPolynomial.X 1)) = MvPolynomial.X 1
      rw [kw_no3a_wdp_mprt_ydeCR_yHomog_X_one, kw_no3a_wdp_mprt_ydeCR_yChartAwayDehom_yZ]

private def kw_no3a_wdp_mprt_ydeCR_yToLoc (V : WeierstrassCurve.Projective R) :
    MvPolynomial (Fin 3) R →+* Localization.Away (X 1 : MvPolynomial (Fin 3) R) :=
  ((kw_no3a_wdp_mprt_ydeCR_yToVal (R := R)).comp (kw_no3a_wdp_mprt_ydeCR_yHomog V)).comp
    (kw_no3a_wdp_mprt_ydeCR_dehomY (R := R)).toRingHom

private theorem kw_no3a_wdp_mprt_ydeCR_yToLoc_X_one (V : WeierstrassCurve.Projective R) :
    kw_no3a_wdp_mprt_ydeCR_yToLoc V (X 1) = 1 := by
  show kw_no3a_wdp_mprt_ydeCR_yToVal (R := R)
      (kw_no3a_wdp_mprt_ydeCR_yHomog V (kw_no3a_wdp_mprt_ydeCR_dehomY (X 1))) = 1
  rw [kw_no3a_wdp_mprt_ydeCR_dehomY_X_one, map_one, map_one]

private theorem kw_no3a_wdp_mprt_ydeCR_yToLoc_X_zero (V : WeierstrassCurve.Projective R) :
    kw_no3a_wdp_mprt_ydeCR_yToLoc V (X 0)
      = Localization.mk (X 0 : MvPolynomial (Fin 3) R)
          (⟨X 1, 1, pow_one _⟩ : Submonoid.powers (X 1 : MvPolynomial (Fin 3) R)) := by
  show kw_no3a_wdp_mprt_ydeCR_yToVal (R := R)
      (kw_no3a_wdp_mprt_ydeCR_yHomog V (kw_no3a_wdp_mprt_ydeCR_dehomY (X 0))) = _
  rw [kw_no3a_wdp_mprt_ydeCR_dehomY_X_zero, kw_no3a_wdp_mprt_ydeCR_yHomog_X_zero,
    kw_no3a_wdp_mprt_ydeCR_yToVal_eq_val, kw_no3a_wdp_mprt_ydeCR_yX_val]

private theorem kw_no3a_wdp_mprt_ydeCR_yToLoc_X_two (V : WeierstrassCurve.Projective R) :
    kw_no3a_wdp_mprt_ydeCR_yToLoc V (X 2)
      = Localization.mk (X 2 : MvPolynomial (Fin 3) R)
          (⟨X 1, 1, pow_one _⟩ : Submonoid.powers (X 1 : MvPolynomial (Fin 3) R)) := by
  show kw_no3a_wdp_mprt_ydeCR_yToVal (R := R)
      (kw_no3a_wdp_mprt_ydeCR_yHomog V (kw_no3a_wdp_mprt_ydeCR_dehomY (X 2))) = _
  rw [kw_no3a_wdp_mprt_ydeCR_dehomY_X_two, kw_no3a_wdp_mprt_ydeCR_yHomog_X_one,
    kw_no3a_wdp_mprt_ydeCR_yToVal_eq_val, kw_no3a_wdp_mprt_ydeCR_yZ_val]

private theorem kw_no3a_wdp_mprt_ydeCR_yToLoc_C (V : WeierstrassCurve.Projective R) (r : R) :
    kw_no3a_wdp_mprt_ydeCR_yToLoc V (C r)
      = algebraMap (MvPolynomial (Fin 3) R)
          (Localization.Away (X 1 : MvPolynomial (Fin 3) R)) (C r) := by
  show kw_no3a_wdp_mprt_ydeCR_yToVal (R := R)
      (kw_no3a_wdp_mprt_ydeCR_yHomog V (kw_no3a_wdp_mprt_ydeCR_dehomY (C r))) = _
  rw [kw_no3a_wdp_mprt_ydeCR_dehomY_C, kw_no3a_wdp_mprt_ydeCR_yHomog_C,
    kw_no3a_wdp_mprt_ydeCR_yToVal_eq_val, kw_no3a_wdp_mprt_aqcCR_ambientFromR_val,
    ← Localization.mk_one_eq_algebraMap]

private theorem kw_no3a_wdp_mprt_ydeCR_yToLoc_X_zero_mul (V : WeierstrassCurve.Projective R) :
    kw_no3a_wdp_mprt_ydeCR_yToLoc V (X 0)
        * algebraMap (MvPolynomial (Fin 3) R)
            (Localization.Away (X 1 : MvPolynomial (Fin 3) R)) (X 1)
      = algebraMap (MvPolynomial (Fin 3) R)
          (Localization.Away (X 1 : MvPolynomial (Fin 3) R)) (X 0) := by
  rw [kw_no3a_wdp_mprt_ydeCR_yToLoc_X_zero, Localization.mk_eq_mk'_apply]
  exact IsLocalization.mk'_spec _ (X 0 : MvPolynomial (Fin 3) R)
    (⟨X 1, 1, pow_one _⟩ : Submonoid.powers (X 1 : MvPolynomial (Fin 3) R))

private theorem kw_no3a_wdp_mprt_ydeCR_yToLoc_X_two_mul (V : WeierstrassCurve.Projective R) :
    kw_no3a_wdp_mprt_ydeCR_yToLoc V (X 2)
        * algebraMap (MvPolynomial (Fin 3) R)
            (Localization.Away (X 1 : MvPolynomial (Fin 3) R)) (X 1)
      = algebraMap (MvPolynomial (Fin 3) R)
          (Localization.Away (X 1 : MvPolynomial (Fin 3) R)) (X 2) := by
  rw [kw_no3a_wdp_mprt_ydeCR_yToLoc_X_two, Localization.mk_eq_mk'_apply]
  exact IsLocalization.mk'_spec _ (X 2 : MvPolynomial (Fin 3) R)
    (⟨X 1, 1, pow_one _⟩ : Submonoid.powers (X 1 : MvPolynomial (Fin 3) R))

private theorem kw_no3a_wdp_mprt_ydeCR_yToLoc_monomial (V : WeierstrassCurve.Projective R)
    (d : Fin 3 →₀ ℕ) (c : R) (n : ℕ) (hn : d 0 + d 1 + d 2 = n) :
    kw_no3a_wdp_mprt_ydeCR_yToLoc V (monomial d c)
      = Localization.mk (monomial d c)
          (⟨X 1 ^ n, n, rfl⟩ : Submonoid.powers (X 1 : MvPolynomial (Fin 3) R)) := by
  rw [Localization.mk_eq_mk'_apply, IsLocalization.eq_mk'_iff_mul_eq]
  show kw_no3a_wdp_mprt_ydeCR_yToLoc V (monomial d c)
        * algebraMap (MvPolynomial (Fin 3) R)
            (Localization.Away (X 1 : MvPolynomial (Fin 3) R)) (X 1 ^ n)
      = algebraMap (MvPolynomial (Fin 3) R)
          (Localization.Away (X 1 : MvPolynomial (Fin 3) R)) (monomial d c)
  rw [monomial_eq_C_mul_pow]
  simp only [map_mul, map_pow]
  rw [kw_no3a_wdp_mprt_ydeCR_yToLoc_C, kw_no3a_wdp_mprt_ydeCR_yToLoc_X_one, one_pow, mul_one,
    ← hn, pow_add, pow_add, ← kw_no3a_wdp_mprt_ydeCR_yToLoc_X_zero_mul,
    ← kw_no3a_wdp_mprt_ydeCR_yToLoc_X_two_mul, mul_pow, mul_pow]
  ring

private theorem kw_no3a_wdp_mprt_ydeCR_yToLoc_isHomogeneous (V : WeierstrassCurve.Projective R)
    (n : ℕ) (a : MvPolynomial (Fin 3) R) (ha : a.IsHomogeneous n) :
    kw_no3a_wdp_mprt_ydeCR_yToLoc V a
      = Localization.mk a
          (⟨X 1 ^ n, n, rfl⟩ : Submonoid.powers (X 1 : MvPolynomial (Fin 3) R)) := by
  conv_lhs => rw [MvPolynomial.as_sum a]
  conv_rhs => rw [MvPolynomial.as_sum a]
  rw [map_sum, Localization.mk_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdeg : d.degree = n := by
    by_contra hne
    exact MvPolynomial.mem_support_iff.mp hd (ha.coeff_eq_zero hne)
  exact kw_no3a_wdp_mprt_ydeCR_yToLoc_monomial V d (MvPolynomial.coeff d a) n
    (by rw [← hdeg, Finsupp.degree_eq_sum, Fin.sum_univ_three])

private theorem kw_no3a_wdp_mprt_ydeCR_homog_comp_dehom (V : WeierstrassCurve.Projective R) :
    (kw_no3a_wdp_mprt_ydeCR_yHomog V).comp
        (kw_no3a_wdp_mprt_ydeCR_yChartAwayDehom (R := R))
      = RingHom.id (HomogeneousLocalization.Away (homogeneousSubmodule (Fin 3) R)
          (X 1 : MvPolynomial (Fin 3) R)) := by
  refine RingHom.ext fun z => ?_
  obtain ⟨n, a, ha, rfl⟩ := HomogeneousLocalization.Away.mk_surjective
    (homogeneousSubmodule (Fin 3) R) (X_mem_homogeneousSubmodule_one R 1) z
  apply HomogeneousLocalization.val_injective
  rw [RingHom.comp_apply, RingHom.id_apply, kw_no3a_wdp_mprt_ydeCR_yChartAwayDehom_awayMk]
  have key : kw_no3a_wdp_mprt_ydeCR_yToLoc V a
      = Localization.mk a
          (⟨X 1 ^ n, n, rfl⟩ : Submonoid.powers (X 1 : MvPolynomial (Fin 3) R)) :=
    kw_no3a_wdp_mprt_ydeCR_yToLoc_isHomogeneous V n a
      ((MvPolynomial.mem_homogeneousSubmodule n a).mp (by simpa using ha))
  exact key

private def kw_no3a_wdp_mprt_ydeCR_yChartPolyEquiv (V : WeierstrassCurve.Projective R) :
    HomogeneousLocalization.Away (homogeneousSubmodule (Fin 3) R)
        (X 1 : MvPolynomial (Fin 3) R) ≃+* MvPolynomial (Fin 2) R :=
  RingEquiv.ofRingHom (kw_no3a_wdp_mprt_ydeCR_yChartAwayDehom (R := R))
    (kw_no3a_wdp_mprt_ydeCR_yHomog V)
    (kw_no3a_wdp_mprt_ydeCR_dehom_comp_homog V)
    (kw_no3a_wdp_mprt_ydeCR_homog_comp_dehom V)

private theorem kw_no3a_wdp_mprt_ydeCR_yChartPolyEquiv_apply (V : WeierstrassCurve.Projective R)
    (z : HomogeneousLocalization.Away (homogeneousSubmodule (Fin 3) R)
      (X 1 : MvPolynomial (Fin 3) R)) :
    kw_no3a_wdp_mprt_ydeCR_yChartPolyEquiv V z
      = kw_no3a_wdp_mprt_ydeCR_yChartAwayDehom (R := R) z :=
  rfl

private def kw_no3a_wdp_mprt_ydeCR_yAP (V : WeierstrassCurve.Projective R) :
    HomogeneousLocalization.Away (homogeneousSubmodule (Fin 3) R)
        (X 1 : MvPolynomial (Fin 3) R) →+* kw_no3a_wdp_mprt_ydeCR_coordRing V :=
  (Ideal.Quotient.mk _).comp (kw_no3a_wdp_mprt_ydeCR_yChartAwayDehom (R := R))

private theorem kw_no3a_wdp_mprt_ydeCR_span_range_eq (V : WeierstrassCurve.Projective R) :
    Ideal.span (Set.range (fun _ : Fin 1 => kw_no3a_wdp_mprt_ydeCR_W_Y V))
      = Ideal.span {kw_no3a_wdp_mprt_ydeCR_W_Y V} := by
  congr 1
  exact Set.range_const

private theorem kw_no3a_wdp_mprt_ydeCR_yAP_surjective (V : WeierstrassCurve.Projective R) :
    Function.Surjective (kw_no3a_wdp_mprt_ydeCR_yAP V) := by
  intro y
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective y
  exact ⟨(kw_no3a_wdp_mprt_ydeCR_yChartPolyEquiv V).symm p, by
    rw [kw_no3a_wdp_mprt_ydeCR_yAP, RingHom.comp_apply,
      ← kw_no3a_wdp_mprt_ydeCR_yChartPolyEquiv_apply, RingEquiv.apply_symm_apply]⟩

private theorem kw_no3a_wdp_mprt_ydeCR_yChartAwayDehom_W_loc (V : WeierstrassCurve.Projective R) :
    kw_no3a_wdp_mprt_ydeCR_yChartAwayDehom (R := R) (kw_no3a_wdp_mprt_aqcCR_W_loc V 1)
      = kw_no3a_wdp_mprt_ydeCR_W_Y V := by
  unfold kw_no3a_wdp_mprt_aqcCR_W_loc
  rw [kw_no3a_wdp_mprt_ydeCR_yChartAwayDehom_awayMk, kw_no3a_wdp_mprt_ydeCR_dehomY_polynomial]

private theorem kw_no3a_wdp_mprt_ydeCR_ker_yAP (V : WeierstrassCurve.Projective R) :
    RingHom.ker (kw_no3a_wdp_mprt_ydeCR_yAP V)
      = Ideal.span {kw_no3a_wdp_mprt_aqcCR_W_loc V 1} := by
  refine le_antisymm ?_ (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr
    (RingHom.mem_ker.mpr ?_)))
  · intro x hx
    rw [RingHom.mem_ker, kw_no3a_wdp_mprt_ydeCR_yAP, RingHom.comp_apply,
      Ideal.Quotient.eq_zero_iff_mem, kw_no3a_wdp_mprt_ydeCR_span_range_eq,
      Ideal.mem_span_singleton'] at hx
    obtain ⟨q, hq⟩ := hx
    refine Ideal.mem_span_singleton'.mpr ⟨(kw_no3a_wdp_mprt_ydeCR_yChartPolyEquiv V).symm q, ?_⟩
    apply (kw_no3a_wdp_mprt_ydeCR_yChartPolyEquiv V).injective
    rw [map_mul, RingEquiv.apply_symm_apply, kw_no3a_wdp_mprt_ydeCR_yChartPolyEquiv_apply,
      kw_no3a_wdp_mprt_ydeCR_yChartAwayDehom_W_loc,
      kw_no3a_wdp_mprt_ydeCR_yChartPolyEquiv_apply, hq]
  · rw [kw_no3a_wdp_mprt_ydeCR_yAP, RingHom.comp_apply,
      kw_no3a_wdp_mprt_ydeCR_yChartAwayDehom_W_loc, Ideal.Quotient.eq_zero_iff_mem,
      kw_no3a_wdp_mprt_ydeCR_span_range_eq]
    exact Ideal.mem_span_singleton_self _

private theorem kw_no3a_wdp_mprt_ydeCR_yAP_comp_ambientFromR (V : WeierstrassCurve.Projective R) :
    (kw_no3a_wdp_mprt_ydeCR_yAP V).comp (kw_no3a_wdp_mprt_aqcCR_ambientFromR V 1)
      = algebraMap R (kw_no3a_wdp_mprt_ydeCR_coordRing V) := by
  refine RingHom.ext fun r => ?_
  rw [kw_no3a_wdp_mprt_ydeCR_yAP, RingHom.comp_apply, RingHom.comp_apply,
    kw_no3a_wdp_mprt_ydeCR_yChartAwayDehom_const]
  rfl

private abbrev KwNo3aWdpMprtYChartAwayAffineCoordRingBridgeCR
    (V : WeierstrassCurve.Projective R) : Prop :=
  ∃ f : (HomogeneousLocalization.Away (projModelGradingCR V)
          (Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal
            (X 1 : MvPolynomial (Fin 3) R)))
        →+* kw_no3a_wdp_mprt_ydeCR_coordRing V,
    Function.Bijective f
    ∧ f.comp (kw_no3a_wdp_mprt_zcdCR_fromR V 1)
        = algebraMap R (kw_no3a_wdp_mprt_ydeCR_coordRing V)

set_option maxHeartbeats 80000000 in

private theorem kw_no3a_wdp_mprt_ydeCR_yBridge_holds (V : WeierstrassCurve.Projective R) :
    KwNo3aWdpMprtYChartAwayAffineCoordRingBridgeCR V := by
  exact kw_no3a_wdp_mprt_aqcCR_bridge_of_ambientPresent V 1
    (kw_no3a_wdp_mprt_ydeCR_yAP V)
    (algebraMap R (kw_no3a_wdp_mprt_ydeCR_coordRing V))
    (kw_no3a_wdp_mprt_ydeCR_yAP_surjective V) (kw_no3a_wdp_mprt_ydeCR_ker_yAP V)
    (kw_no3a_wdp_mprt_ydeCR_yAP_comp_ambientFromR V)

end WeierstrassProjModel

end

noncomputable section

set_option maxHeartbeats 6400000
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousIdealQuotientGrading
open ProjWeierstrassCubicPrime ProjWeierstrassDehomog

namespace WeierstrassProjModel
p2m_export "WeierstrassProjModel" "projModelHomogeneousIdealCR projModelHomogeneousIdealCR_toIdeal projModelGradingCR projModelStrCR exists_ringEquiv_zChartAwayDegreeZero projModelStrCR_smooth_of_zChartBridge_of_yChartSmooth"
p2m_open "WeierstrassProjModel"

variable {R : Type} [CommRing R]

private theorem kw_no3a_wdp_mprt_ycdCR_algHom_pderiv0 {L : Type*} [CommRing L] [Algebra R L]
    (π : MvPolynomial (Fin 2) R →ₐ[R] L) (V : WeierstrassCurve.Projective R) :
    π (MvPolynomial.pderiv 0 (kw_no3a_wdp_mprt_ydeCR_W_Y V))
      = MvPolynomial.eval
          ![π (MvPolynomial.X 0), 1, π (MvPolynomial.X 1)]
          (V.map (algebraMap R L)).polynomialX := by
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  rw [WeierstrassCurve.Projective.eval_polynomialX]
  simp only [kw_no3a_wdp_mprt_ydeCR_W_Y, map_sub, map_add, MvPolynomial.pderiv_mul,
    MvPolynomial.pderiv_pow, MvPolynomial.pderiv_C, MvPolynomial.pderiv_X_self,
    MvPolynomial.pderiv_X_of_ne h10, mul_zero, zero_mul, add_zero, zero_add, mul_one,
    map_mul, map_pow, map_natCast,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons,
    WeierstrassCurve.map, kw_no3a_wdp_mprt_ydeCR_algHom_C]
  push_cast
  ring

private theorem kw_no3a_wdp_mprt_ycdCR_algHom_pderiv1 {L : Type*} [CommRing L] [Algebra R L]
    (π : MvPolynomial (Fin 2) R →ₐ[R] L) (V : WeierstrassCurve.Projective R) :
    π (MvPolynomial.pderiv 1 (kw_no3a_wdp_mprt_ydeCR_W_Y V))
      = MvPolynomial.eval
          ![π (MvPolynomial.X 0), 1, π (MvPolynomial.X 1)]
          (V.map (algebraMap R L)).polynomialZ := by
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  rw [WeierstrassCurve.Projective.eval_polynomialZ]
  simp only [kw_no3a_wdp_mprt_ydeCR_W_Y, map_sub, map_add, MvPolynomial.pderiv_mul,
    MvPolynomial.pderiv_pow, MvPolynomial.pderiv_C, MvPolynomial.pderiv_X_self,
    MvPolynomial.pderiv_X_of_ne h01, mul_zero, zero_mul, add_zero, zero_add, mul_one,
    map_mul, map_pow, map_natCast, map_one,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons,
    WeierstrassCurve.map, kw_no3a_wdp_mprt_ydeCR_algHom_C]
  push_cast
  ring

private noncomputable def kw_no3a_wdp_mprt_ycdCR_P₀ (V : WeierstrassCurve.Projective R) (j : Fin 2) :
    Algebra.PreSubmersivePresentation R (kw_no3a_wdp_mprt_ydeCR_coordRing V) (Fin 2) (Fin 1) :=
  Algebra.PreSubmersivePresentation.naive (v := fun _ : Fin 1 => kw_no3a_wdp_mprt_ydeCR_W_Y V)
    (fun _ : Fin 1 => j) (Function.injective_of_subsingleton _)

private theorem kw_no3a_wdp_mprt_ycdCR_P₀_jacobian (V : WeierstrassCurve.Projective R) (j : Fin 2) :
    (kw_no3a_wdp_mprt_ycdCR_P₀ V j).jacobian = kw_no3a_wdp_mprt_ydeCR_mkYPartial V j := by
  classical
  rw [kw_no3a_wdp_mprt_ycdCR_P₀, Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det,
    Matrix.det_unique]
  simp only [Algebra.PreSubmersivePresentation.jacobiMatrix_naive, Fin.default_eq_zero]
  rfl

private noncomputable def kw_no3a_wdp_mprt_ycdCR_compPres (V : WeierstrassCurve.Projective R)
    (j : Fin 2) :
    Algebra.PreSubmersivePresentation R
      (Localization.Away (kw_no3a_wdp_mprt_ydeCR_mkYPartial V j))
      (Unit ⊕ Fin 2) (Unit ⊕ Fin 1) :=
  (Algebra.PreSubmersivePresentation.localizationAway
    (Localization.Away (kw_no3a_wdp_mprt_ydeCR_mkYPartial V j))
    (kw_no3a_wdp_mprt_ydeCR_mkYPartial V j)).comp (kw_no3a_wdp_mprt_ycdCR_P₀ V j)

private theorem kw_no3a_wdp_mprt_ycdCR_compPres_jacobian_isUnit (V : WeierstrassCurve.Projective R)
    (j : Fin 2) :
    IsUnit (kw_no3a_wdp_mprt_ycdCR_compPres V j).jacobian := by
  rw [kw_no3a_wdp_mprt_ycdCR_compPres,
    Algebra.PreSubmersivePresentation.comp_jacobian_eq_jacobian_smul_jacobian,
    Algebra.PreSubmersivePresentation.localizationAway_jacobian,
    kw_no3a_wdp_mprt_ycdCR_P₀_jacobian, Algebra.smul_def]
  exact (IsLocalization.Away.algebraMap_isUnit (kw_no3a_wdp_mprt_ydeCR_mkYPartial V j)).mul
    (IsLocalization.Away.algebraMap_isUnit (kw_no3a_wdp_mprt_ydeCR_mkYPartial V j))

private noncomputable def kw_no3a_wdp_mprt_ycdCR_submersive (V : WeierstrassCurve.Projective R)
    (j : Fin 2) :
    Algebra.SubmersivePresentation R
      (Localization.Away (kw_no3a_wdp_mprt_ydeCR_mkYPartial V j))
      (Unit ⊕ Fin 2) (Unit ⊕ Fin 1) where
  __ := kw_no3a_wdp_mprt_ycdCR_compPres V j
  jacobian_isUnit := kw_no3a_wdp_mprt_ycdCR_compPres_jacobian_isUnit V j

private theorem kw_no3a_wdp_mprt_ycdCR_localizedPartialStandardSmooth
    (V : WeierstrassCurve.Projective R) (j : Fin 2) :
    Algebra.IsStandardSmooth R (Localization.Away (kw_no3a_wdp_mprt_ydeCR_mkYPartial V j)) :=
  (kw_no3a_wdp_mprt_ycdCR_submersive V j).isStandardSmooth

private theorem kw_no3a_wdp_mprt_ycdCR_rep_YOne_ne_zero {L : Type*} [CommRing L] [Nontrivial L]
    (a b : L) :
    (![a, 1, b] : Fin 3 → L) ≠ 0 := by
  intro h
  have h1 : (![a, 1, b] : Fin 3 → L) 1 = 0 := by rw [h]; rfl
  simp only [Matrix.cons_val_one] at h1
  exact one_ne_zero h1

private theorem kw_no3a_wdp_mprt_ycdCR_not_singular_at_YOne {L : Type*} [Field L]
    (V : WeierstrassCurve.Projective R) [V.IsElliptic] (φ : R →+* L) (x₀ z₀ : L)
    (hW : MvPolynomial.eval ![x₀, 1, z₀] (V.map φ).polynomial = 0)
    (hX : MvPolynomial.eval ![x₀, 1, z₀] (V.map φ).polynomialX = 0)
    (hZ : MvPolynomial.eval ![x₀, 1, z₀] (V.map φ).polynomialZ = 0) :
    False := by
  have hns := ProjWeierstrassDehomog.nonsingular_of_equation_of_ne_zero
    (V := V.map φ) hW (kw_no3a_wdp_mprt_ycdCR_rep_YOne_ne_zero x₀ z₀)
  have hY : MvPolynomial.eval ![x₀, 1, z₀] (V.map φ).polynomialY = 0 := by
    have hEul := WeierstrassCurve.Projective.polynomial_relation (W' := V.map φ) ![x₀, 1, z₀]
    simp only [hW, hX, hZ, mul_zero, zero_add, add_zero,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons, one_mul] at hEul
    exact hEul.symm
  rcases hns.2 with h | h | h
  · exact h hX
  · exact h hY
  · exact h hZ

private theorem kw_no3a_wdp_mprt_ycdCR_no_maximal_over_triple
    (V : WeierstrassCurve.Projective R) [V.IsElliptic]
    (M : Ideal (MvPolynomial (Fin 2) R)) (hmax : M.IsMaximal)
    (hW : kw_no3a_wdp_mprt_ydeCR_W_Y V ∈ M)
    (hX : MvPolynomial.pderiv 0 (kw_no3a_wdp_mprt_ydeCR_W_Y V) ∈ M)
    (hZ : MvPolynomial.pderiv 1 (kw_no3a_wdp_mprt_ydeCR_W_Y V) ∈ M) :
    False := by
  classical
  haveI := hmax
  letI : Field (MvPolynomial (Fin 2) R ⧸ M) := Ideal.Quotient.field M

  have hbrW := @kw_no3a_wdp_mprt_ydeCR_algHom_W_Y R _ (MvPolynomial (Fin 2) R ⧸ M)
    inferInstance inferInstance (Ideal.Quotient.mkₐ R M) V
  have hbrX := @kw_no3a_wdp_mprt_ycdCR_algHom_pderiv0 R _ (MvPolynomial (Fin 2) R ⧸ M)
    inferInstance inferInstance (Ideal.Quotient.mkₐ R M) V
  have hbrZ := @kw_no3a_wdp_mprt_ycdCR_algHom_pderiv1 R _ (MvPolynomial (Fin 2) R ⧸ M)
    inferInstance inferInstance (Ideal.Quotient.mkₐ R M) V
  simp only [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem.mpr hW,
    Ideal.Quotient.eq_zero_iff_mem.mpr hX, Ideal.Quotient.eq_zero_iff_mem.mpr hZ]
    at hbrW hbrX hbrZ
  exact kw_no3a_wdp_mprt_ycdCR_not_singular_at_YOne V
    (algebraMap R (MvPolynomial (Fin 2) R ⧸ M)) _ _ hbrW.symm hbrX.symm hbrZ.symm

private theorem kw_no3a_wdp_mprt_ycdCR_partialsSpanTop
    (V : WeierstrassCurve.Projective R) [V.IsElliptic] :
    Ideal.span (Set.range (kw_no3a_wdp_mprt_ydeCR_mkYPartial V)) = ⊤ := by
  classical
  by_contra hne
  obtain ⟨m, hmax, hle⟩ :=
    Ideal.exists_le_maximal (Ideal.span (Set.range (kw_no3a_wdp_mprt_ydeCR_mkYPartial V))) hne
  let M : Ideal (MvPolynomial (Fin 2) R) :=
    Ideal.comap (Ideal.Quotient.mk
      (Ideal.span (Set.range (fun _ : Fin 1 => kw_no3a_wdp_mprt_ydeCR_W_Y V)))) m
  have hMmax : M.IsMaximal :=
    Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
  have hWM : kw_no3a_wdp_mprt_ydeCR_W_Y V ∈ M := by
    have hspan : kw_no3a_wdp_mprt_ydeCR_W_Y V
        ∈ Ideal.span (Set.range (fun _ : Fin 1 => kw_no3a_wdp_mprt_ydeCR_W_Y V)) :=
      Ideal.subset_span (Set.mem_range_self (0 : Fin 1))
    simp only [M, Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hspan]
    exact Submodule.zero_mem m
  have hXM : MvPolynomial.pderiv 0 (kw_no3a_wdp_mprt_ydeCR_W_Y V) ∈ M := by
    have h0 : kw_no3a_wdp_mprt_ydeCR_mkYPartial V 0 ∈ m := hle (Ideal.subset_span ⟨0, rfl⟩)
    simpa only [kw_no3a_wdp_mprt_ydeCR_mkYPartial, M, Ideal.mem_comap] using h0
  have hZM : MvPolynomial.pderiv 1 (kw_no3a_wdp_mprt_ydeCR_W_Y V) ∈ M := by
    have h1 : kw_no3a_wdp_mprt_ydeCR_mkYPartial V 1 ∈ m := hle (Ideal.subset_span ⟨1, rfl⟩)
    simpa only [kw_no3a_wdp_mprt_ydeCR_mkYPartial, M, Ideal.mem_comap] using h1
  exact kw_no3a_wdp_mprt_ycdCR_no_maximal_over_triple V M hMmax hWM hXM hZM

private theorem kw_no3a_wdp_mprt_ycdCR_coordRing_smooth
    (V : WeierstrassCurve.Projective R) [V.IsElliptic] :
    Algebra.Smooth R (kw_no3a_wdp_mprt_ydeCR_coordRing V) := by
  rw [← RingHom.smooth_algebraMap, RingHom.smooth_iff_locally_isStandardSmooth]
  refine ⟨Set.range (kw_no3a_wdp_mprt_ydeCR_mkYPartial V),
    kw_no3a_wdp_mprt_ycdCR_partialsSpanTop V, ?_⟩
  rintro t ⟨j, rfl⟩
  rw [← IsScalarTower.algebraMap_eq, RingHom.isStandardSmooth_algebraMap]
  exact kw_no3a_wdp_mprt_ycdCR_localizedPartialStandardSmooth V j

attribute [local instance] MvPolynomial.gradedAlgebra

private theorem kw_no3a_wdp_mprt_ycdCR_yChartFromRSmoothCR_of_bridge
    (V : WeierstrassCurve.Projective R) [V.IsElliptic]
    (hybr : KwNo3aWdpMprtYChartAwayAffineCoordRingBridgeCR V) :
    KwNo3aWdpMprtYChartFromRSmoothCR V := by
  obtain ⟨f, hbij, hecomp⟩ := hybr
  let e := RingEquiv.ofBijective f hbij
  have halg : RingHom.Smooth (algebraMap R (kw_no3a_wdp_mprt_ydeCR_coordRing V)) :=
    RingHom.smooth_algebraMap.mpr (kw_no3a_wdp_mprt_ycdCR_coordRing_smooth V)
  have h3 := RingHom.Smooth.respectsIso.1 _ e.symm halg
  have hkey : e.symm.toRingHom.comp (algebraMap R (kw_no3a_wdp_mprt_ydeCR_coordRing V))
      = kw_no3a_wdp_mprt_zcdCR_fromR V 1 := by
    rw [← hecomp]
    exact RingHom.ext fun x => e.symm_apply_apply _
  rw [hkey] at h3
  exact h3

private theorem kw_no3a_wdp_mprt_ycdCR_yChartFromRSmoothCR_holds
    (V : WeierstrassCurve.Projective R) [V.IsElliptic] :
    KwNo3aWdpMprtYChartFromRSmoothCR V :=
  kw_no3a_wdp_mprt_ycdCR_yChartFromRSmoothCR_of_bridge V
    (kw_no3a_wdp_mprt_ydeCR_yBridge_holds V)

private theorem kw_no3a_wdp_mprt_ycdCR_smooth_projModelStrCR_holds
    (V : WeierstrassCurve.Projective R) [V.IsElliptic] :
    Smooth (projModelStrCR V) :=
  kw_no3a_wdp_mprt_aqcCR_smooth_projModelStrCR_of_yFromR V
    (kw_no3a_wdp_mprt_ycdCR_yChartFromRSmoothCR_holds V)

end WeierstrassProjModel

end

theorem solution {R : Type} [CommRing R]
    (V : WeierstrassCurve.Projective R) [V.IsElliptic] :
    AlgebraicGeometry.Smooth (WeierstrassProjModel.projModelStrCR V) :=
  WeierstrassProjModel.kw_no3a_wdp_mprt_ycdCR_smooth_projModelStrCR_holds V

end S_WeierstrassProjModel_projModelStrCR_smooth
end P2MW
export P2MW.S_WeierstrassProjModel_projModelStrCR_smooth (solution)
