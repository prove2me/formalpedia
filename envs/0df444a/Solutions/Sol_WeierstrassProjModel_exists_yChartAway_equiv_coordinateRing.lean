-- Prove2me | solution 1 for WeierstrassProjModel.exists_yChartAway_equiv_coordinateRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/d4786f25-5072-57d9-bf39-b0d1d3d8ac6b

import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.Localization.Away.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassProjModel_exists_yChartAway_equiv_coordinateRing

universe u

section MEGA_prelude_y_lean

end MEGA_prelude_y_lean

section MEGA_ProjectiveWeierstrassZChartAwayDegreeZero_lean

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

end ChartElements

section ForwardMap

variable {R : Type*} [CommRing R]

end ForwardMap

section BackwardMap

variable {R : Type*} [CommRing R]

end BackwardMap

section HomogenisationIdentity

variable {R : Type*} [CommRing R]

theorem monomial_eq_C_mul_pow (d : Fin 3 →₀ ℕ) (c : R) :
    (monomial d c : MvPolynomial (Fin 3) R)
      = C c * (X 0 ^ d 0 * X 1 ^ d 1 * X 2 ^ d 2) := by
  rw [MvPolynomial.monomial_eq, Finsupp.prod_fintype _ _ fun i => pow_zero _,
    Fin.prod_univ_three]

end HomogenisationIdentity

section CompositeIdentities

variable {R : Type*} [CommRing R]

end CompositeIdentities

section Isomorphisms

variable {R : Type*} [CommRing R]

end Isomorphisms

end ProjWeierstrassDehomog

end

end MEGA_ProjectiveWeierstrassZChartAwayDegreeZero_lean

section MEGA_KwNo3aWdpMprtZChartSmoothCRDischarge_lean

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousIdealQuotientGrading
open ProjWeierstrassCubicPrime HomogeneousLocalization

namespace WeierstrassProjModel
p2m_export "WeierstrassProjModel" "projModelHomogeneousIdealCR projModelHomogeneousIdealCR_toIdeal projModelGradingCR"
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
p2m_export "WeierstrassProjModel" "projModelHomogeneousIdealCR projModelHomogeneousIdealCR_toIdeal projModelGradingCR"
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

theorem kw_no3a_wdp_mprt_aqcCR_ambientFromR_val (V : WeierstrassCurve.Projective R)
    (i : Fin 3) (r : R) :
    (kw_no3a_wdp_mprt_aqcCR_ambientFromR V i r).val
      = Localization.mk (C r : MvPolynomial (Fin 3) R)
          (1 : Submonoid.powers (X i : MvPolynomial (Fin 3) R)) :=
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

end WeierstrassProjModel

end

end MEGA_KwNo3aWdpMprtZBridgeCRDischarge_lean

section MEGA_KwNo3aWdpMprtYChartDehomEngineCR_lean

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option linter.unusedSectionVars false

noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousIdealQuotientGrading
open ProjWeierstrassCubicPrime ProjWeierstrassDehomog

namespace WeierstrassProjModel
p2m_export "WeierstrassProjModel" "projModelHomogeneousIdealCR projModelHomogeneousIdealCR_toIdeal projModelGradingCR"
p2m_open "WeierstrassProjModel"

attribute [local instance] MvPolynomial.gradedAlgebra

variable {R : Type u} [CommRing R]

theorem kw_no3a_wdp_mprt_ydeCR_algHom_C {L : Type*} [CommRing L] [Algebra R L]
    (π : MvPolynomial (Fin 2) R →ₐ[R] L) (r : R) :
    π (MvPolynomial.C r) = algebraMap R L r := by
  rw [← MvPolynomial.algebraMap_eq]; exact π.commutes r

noncomputable def kw_no3a_wdp_mprt_ydeCR_W_Y (V : WeierstrassCurve.Projective R) :
    MvPolynomial (Fin 2) R :=
  MvPolynomial.X 1
    + MvPolynomial.C V.a₁ * MvPolynomial.X 0 * MvPolynomial.X 1
    + MvPolynomial.C V.a₃ * (MvPolynomial.X 1) ^ 2
    - ((MvPolynomial.X 0) ^ 3
        + MvPolynomial.C V.a₂ * (MvPolynomial.X 0) ^ 2 * MvPolynomial.X 1
        + MvPolynomial.C V.a₄ * MvPolynomial.X 0 * (MvPolynomial.X 1) ^ 2
        + MvPolynomial.C V.a₆ * (MvPolynomial.X 1) ^ 3)

abbrev kw_no3a_wdp_mprt_ydeCR_coordRing (V : WeierstrassCurve.Projective R) : Type u :=
  MvPolynomial (Fin 2) R
    ⧸ Ideal.span (Set.range (fun _ : Fin 1 => kw_no3a_wdp_mprt_ydeCR_W_Y V))

theorem kw_no3a_wdp_mprt_ydeCR_algHom_W_Y {L : Type*} [CommRing L] [Algebra R L]
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

noncomputable def kw_no3a_wdp_mprt_ydeCR_dehomY :
    MvPolynomial (Fin 3) R →ₐ[R] MvPolynomial (Fin 2) R :=
  MvPolynomial.aeval ![MvPolynomial.X 0, 1, MvPolynomial.X 1]

theorem kw_no3a_wdp_mprt_ydeCR_dehomY_X_zero :
    kw_no3a_wdp_mprt_ydeCR_dehomY (X 0 : MvPolynomial (Fin 3) R) = MvPolynomial.X 0 := by
  simp [kw_no3a_wdp_mprt_ydeCR_dehomY]

theorem kw_no3a_wdp_mprt_ydeCR_dehomY_X_one :
    kw_no3a_wdp_mprt_ydeCR_dehomY (X 1 : MvPolynomial (Fin 3) R)
      = (1 : MvPolynomial (Fin 2) R) := by
  simp [kw_no3a_wdp_mprt_ydeCR_dehomY]

theorem kw_no3a_wdp_mprt_ydeCR_dehomY_X_two :
    kw_no3a_wdp_mprt_ydeCR_dehomY (X 2 : MvPolynomial (Fin 3) R) = MvPolynomial.X 1 := by
  simp [kw_no3a_wdp_mprt_ydeCR_dehomY]

theorem kw_no3a_wdp_mprt_ydeCR_dehomY_C (r : R) :
    kw_no3a_wdp_mprt_ydeCR_dehomY (C r : MvPolynomial (Fin 3) R) = MvPolynomial.C r := by
  simp [kw_no3a_wdp_mprt_ydeCR_dehomY]

def kw_no3a_wdp_mprt_ydeCR_yX :
    HomogeneousLocalization.Away (homogeneousSubmodule (Fin 3) R)
      (X 1 : MvPolynomial (Fin 3) R) :=
  HomogeneousLocalization.mk
    ⟨1, ⟨X 0, X_mem_homogeneousSubmodule_one R 0⟩, ⟨X 1, X_mem_homogeneousSubmodule_one R 1⟩,
      ⟨1, pow_one _⟩⟩

theorem kw_no3a_wdp_mprt_ydeCR_yX_val :
    (kw_no3a_wdp_mprt_ydeCR_yX (R := R)).val
      = Localization.mk (X 0 : MvPolynomial (Fin 3) R)
          (⟨X 1, 1, pow_one _⟩ : Submonoid.powers (X 1 : MvPolynomial (Fin 3) R)) :=
  rfl

def kw_no3a_wdp_mprt_ydeCR_yZ :
    HomogeneousLocalization.Away (homogeneousSubmodule (Fin 3) R)
      (X 1 : MvPolynomial (Fin 3) R) :=
  HomogeneousLocalization.mk
    ⟨1, ⟨X 2, X_mem_homogeneousSubmodule_one R 2⟩, ⟨X 1, X_mem_homogeneousSubmodule_one R 1⟩,
      ⟨1, pow_one _⟩⟩

theorem kw_no3a_wdp_mprt_ydeCR_yZ_val :
    (kw_no3a_wdp_mprt_ydeCR_yZ (R := R)).val
      = Localization.mk (X 2 : MvPolynomial (Fin 3) R)
          (⟨X 1, 1, pow_one _⟩ : Submonoid.powers (X 1 : MvPolynomial (Fin 3) R)) :=
  rfl

theorem kw_no3a_wdp_mprt_ydeCR_aeval_polynomial {S : Type*} [CommRing S] [Algebra R S]
    (V : WeierstrassCurve.Projective R) (f : Fin 3 → S) :
    MvPolynomial.aeval f V.polynomial
      = MvPolynomial.eval f (V.map (algebraMap R S)).polynomial := by
  rw [WeierstrassCurve.Projective.eval_polynomial, MvPolynomial.aeval_def,
    WeierstrassCurve.Projective.polynomial]
  simp only [eval₂_sub, eval₂_add, eval₂_mul, eval₂_pow, eval₂_X, eval₂_C,
    WeierstrassCurve.map]

theorem kw_no3a_wdp_mprt_ydeCR_dehomY_polynomial (V : WeierstrassCurve.Projective R) :
    kw_no3a_wdp_mprt_ydeCR_dehomY V.polynomial = kw_no3a_wdp_mprt_ydeCR_W_Y V := by
  have h := kw_no3a_wdp_mprt_ydeCR_algHom_W_Y
    (AlgHom.id R (MvPolynomial (Fin 2) R)) V
  simp only [AlgHom.id_apply] at h
  rw [h, kw_no3a_wdp_mprt_ydeCR_dehomY]
  exact kw_no3a_wdp_mprt_ydeCR_aeval_polynomial V ![X 0, 1, X 1]

theorem kw_no3a_wdp_mprt_ydeCR_dehomY_X_one_mul_one :
    (kw_no3a_wdp_mprt_ydeCR_dehomY (R := R)).toRingHom (X 1) * 1 = 1 := by
  show kw_no3a_wdp_mprt_ydeCR_dehomY (X 1 : MvPolynomial (Fin 3) R) * 1 = 1
  rw [kw_no3a_wdp_mprt_ydeCR_dehomY_X_one, mul_one]

def kw_no3a_wdp_mprt_ydeCR_yLocDehom :
    Localization.Away (X 1 : MvPolynomial (Fin 3) R) →+* MvPolynomial (Fin 2) R :=
  Localization.awayLift (kw_no3a_wdp_mprt_ydeCR_dehomY (R := R)).toRingHom (X 1)
    (isUnit_iff_exists_inv.mpr ⟨1, kw_no3a_wdp_mprt_ydeCR_dehomY_X_one_mul_one⟩)

theorem kw_no3a_wdp_mprt_ydeCR_yLocDehom_mk (a : MvPolynomial (Fin 3) R) (n : ℕ) :
    kw_no3a_wdp_mprt_ydeCR_yLocDehom
        (Localization.mk a
          (⟨X 1 ^ n, n, rfl⟩ : Submonoid.powers (X 1 : MvPolynomial (Fin 3) R)))
      = kw_no3a_wdp_mprt_ydeCR_dehomY a := by
  have h := Localization.awayLift_mk (A := MvPolynomial (Fin 2) R)
    (kw_no3a_wdp_mprt_ydeCR_dehomY (R := R)).toRingHom (X 1) a 1
    kw_no3a_wdp_mprt_ydeCR_dehomY_X_one_mul_one n
  rw [one_pow, mul_one] at h
  exact h

def kw_no3a_wdp_mprt_ydeCR_yChartAwayDehom :
    HomogeneousLocalization.Away (homogeneousSubmodule (Fin 3) R)
        (X 1 : MvPolynomial (Fin 3) R) →+* MvPolynomial (Fin 2) R :=
  (kw_no3a_wdp_mprt_ydeCR_yLocDehom (R := R)).comp
    (algebraMap
      (HomogeneousLocalization.Away (homogeneousSubmodule (Fin 3) R)
        (X 1 : MvPolynomial (Fin 3) R))
      (Localization.Away (X 1 : MvPolynomial (Fin 3) R)))

def kw_no3a_wdp_mprt_ydeCR_yToVal :
    HomogeneousLocalization.Away (homogeneousSubmodule (Fin 3) R)
        (X 1 : MvPolynomial (Fin 3) R) →+*
      Localization.Away (X 1 : MvPolynomial (Fin 3) R) :=
  algebraMap
    (HomogeneousLocalization.Away (homogeneousSubmodule (Fin 3) R)
      (X 1 : MvPolynomial (Fin 3) R))
    (Localization.Away (X 1 : MvPolynomial (Fin 3) R))

theorem kw_no3a_wdp_mprt_ydeCR_yToVal_eq_val
    (z : HomogeneousLocalization.Away (homogeneousSubmodule (Fin 3) R)
      (X 1 : MvPolynomial (Fin 3) R)) :
    kw_no3a_wdp_mprt_ydeCR_yToVal (R := R) z = z.val :=
  HomogeneousLocalization.algebraMap_apply z

theorem kw_no3a_wdp_mprt_ydeCR_yChartAwayDehom_awayMk (n : ℕ) (a : MvPolynomial (Fin 3) R)
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

theorem kw_no3a_wdp_mprt_ydeCR_yChartAwayDehom_yX :
    kw_no3a_wdp_mprt_ydeCR_yChartAwayDehom (R := R) kw_no3a_wdp_mprt_ydeCR_yX
      = MvPolynomial.X 0 := by
  show kw_no3a_wdp_mprt_ydeCR_yLocDehom
    (kw_no3a_wdp_mprt_ydeCR_yToVal (R := R) kw_no3a_wdp_mprt_ydeCR_yX) = _
  rw [kw_no3a_wdp_mprt_ydeCR_yToVal_eq_val, kw_no3a_wdp_mprt_ydeCR_yX_val]
  have h1 : (⟨(X 1 : MvPolynomial (Fin 3) R), 1, pow_one _⟩ :
        Submonoid.powers (X 1 : MvPolynomial (Fin 3) R))
      = ⟨X 1 ^ 1, 1, rfl⟩ := Subtype.ext (pow_one _).symm
  rw [h1, kw_no3a_wdp_mprt_ydeCR_yLocDehom_mk, kw_no3a_wdp_mprt_ydeCR_dehomY_X_zero]

theorem kw_no3a_wdp_mprt_ydeCR_yChartAwayDehom_yZ :
    kw_no3a_wdp_mprt_ydeCR_yChartAwayDehom (R := R) kw_no3a_wdp_mprt_ydeCR_yZ
      = MvPolynomial.X 1 := by
  show kw_no3a_wdp_mprt_ydeCR_yLocDehom
    (kw_no3a_wdp_mprt_ydeCR_yToVal (R := R) kw_no3a_wdp_mprt_ydeCR_yZ) = _
  rw [kw_no3a_wdp_mprt_ydeCR_yToVal_eq_val, kw_no3a_wdp_mprt_ydeCR_yZ_val]
  have h1 : (⟨(X 1 : MvPolynomial (Fin 3) R), 1, pow_one _⟩ :
        Submonoid.powers (X 1 : MvPolynomial (Fin 3) R))
      = ⟨X 1 ^ 1, 1, rfl⟩ := Subtype.ext (pow_one _).symm
  rw [h1, kw_no3a_wdp_mprt_ydeCR_yLocDehom_mk, kw_no3a_wdp_mprt_ydeCR_dehomY_X_two]

theorem kw_no3a_wdp_mprt_ydeCR_yChartAwayDehom_const (V : WeierstrassCurve.Projective R)
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

def kw_no3a_wdp_mprt_ydeCR_yHomog (V : WeierstrassCurve.Projective R) :
    MvPolynomial (Fin 2) R →+*
      HomogeneousLocalization.Away (homogeneousSubmodule (Fin 3) R)
        (X 1 : MvPolynomial (Fin 3) R) :=
  MvPolynomial.eval₂Hom (kw_no3a_wdp_mprt_aqcCR_ambientFromR V 1)
    ![kw_no3a_wdp_mprt_ydeCR_yX, kw_no3a_wdp_mprt_ydeCR_yZ]

theorem kw_no3a_wdp_mprt_ydeCR_yHomog_X_zero (V : WeierstrassCurve.Projective R) :
    kw_no3a_wdp_mprt_ydeCR_yHomog V (MvPolynomial.X 0) = kw_no3a_wdp_mprt_ydeCR_yX := by
  simp [kw_no3a_wdp_mprt_ydeCR_yHomog]

theorem kw_no3a_wdp_mprt_ydeCR_yHomog_X_one (V : WeierstrassCurve.Projective R) :
    kw_no3a_wdp_mprt_ydeCR_yHomog V (MvPolynomial.X 1) = kw_no3a_wdp_mprt_ydeCR_yZ := by
  simp [kw_no3a_wdp_mprt_ydeCR_yHomog]

theorem kw_no3a_wdp_mprt_ydeCR_yHomog_C (V : WeierstrassCurve.Projective R) (r : R) :
    kw_no3a_wdp_mprt_ydeCR_yHomog V (MvPolynomial.C r)
      = kw_no3a_wdp_mprt_aqcCR_ambientFromR V 1 r := by
  simp [kw_no3a_wdp_mprt_ydeCR_yHomog]

theorem kw_no3a_wdp_mprt_ydeCR_dehom_comp_homog (V : WeierstrassCurve.Projective R) :
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

def kw_no3a_wdp_mprt_ydeCR_yToLoc (V : WeierstrassCurve.Projective R) :
    MvPolynomial (Fin 3) R →+* Localization.Away (X 1 : MvPolynomial (Fin 3) R) :=
  ((kw_no3a_wdp_mprt_ydeCR_yToVal (R := R)).comp (kw_no3a_wdp_mprt_ydeCR_yHomog V)).comp
    (kw_no3a_wdp_mprt_ydeCR_dehomY (R := R)).toRingHom

theorem kw_no3a_wdp_mprt_ydeCR_yToLoc_X_one (V : WeierstrassCurve.Projective R) :
    kw_no3a_wdp_mprt_ydeCR_yToLoc V (X 1) = 1 := by
  show kw_no3a_wdp_mprt_ydeCR_yToVal (R := R)
      (kw_no3a_wdp_mprt_ydeCR_yHomog V (kw_no3a_wdp_mprt_ydeCR_dehomY (X 1))) = 1
  rw [kw_no3a_wdp_mprt_ydeCR_dehomY_X_one, map_one, map_one]

theorem kw_no3a_wdp_mprt_ydeCR_yToLoc_X_zero (V : WeierstrassCurve.Projective R) :
    kw_no3a_wdp_mprt_ydeCR_yToLoc V (X 0)
      = Localization.mk (X 0 : MvPolynomial (Fin 3) R)
          (⟨X 1, 1, pow_one _⟩ : Submonoid.powers (X 1 : MvPolynomial (Fin 3) R)) := by
  show kw_no3a_wdp_mprt_ydeCR_yToVal (R := R)
      (kw_no3a_wdp_mprt_ydeCR_yHomog V (kw_no3a_wdp_mprt_ydeCR_dehomY (X 0))) = _
  rw [kw_no3a_wdp_mprt_ydeCR_dehomY_X_zero, kw_no3a_wdp_mprt_ydeCR_yHomog_X_zero,
    kw_no3a_wdp_mprt_ydeCR_yToVal_eq_val, kw_no3a_wdp_mprt_ydeCR_yX_val]

theorem kw_no3a_wdp_mprt_ydeCR_yToLoc_X_two (V : WeierstrassCurve.Projective R) :
    kw_no3a_wdp_mprt_ydeCR_yToLoc V (X 2)
      = Localization.mk (X 2 : MvPolynomial (Fin 3) R)
          (⟨X 1, 1, pow_one _⟩ : Submonoid.powers (X 1 : MvPolynomial (Fin 3) R)) := by
  show kw_no3a_wdp_mprt_ydeCR_yToVal (R := R)
      (kw_no3a_wdp_mprt_ydeCR_yHomog V (kw_no3a_wdp_mprt_ydeCR_dehomY (X 2))) = _
  rw [kw_no3a_wdp_mprt_ydeCR_dehomY_X_two, kw_no3a_wdp_mprt_ydeCR_yHomog_X_one,
    kw_no3a_wdp_mprt_ydeCR_yToVal_eq_val, kw_no3a_wdp_mprt_ydeCR_yZ_val]

theorem kw_no3a_wdp_mprt_ydeCR_yToLoc_C (V : WeierstrassCurve.Projective R) (r : R) :
    kw_no3a_wdp_mprt_ydeCR_yToLoc V (C r)
      = algebraMap (MvPolynomial (Fin 3) R)
          (Localization.Away (X 1 : MvPolynomial (Fin 3) R)) (C r) := by
  show kw_no3a_wdp_mprt_ydeCR_yToVal (R := R)
      (kw_no3a_wdp_mprt_ydeCR_yHomog V (kw_no3a_wdp_mprt_ydeCR_dehomY (C r))) = _
  rw [kw_no3a_wdp_mprt_ydeCR_dehomY_C, kw_no3a_wdp_mprt_ydeCR_yHomog_C,
    kw_no3a_wdp_mprt_ydeCR_yToVal_eq_val, kw_no3a_wdp_mprt_aqcCR_ambientFromR_val,
    ← Localization.mk_one_eq_algebraMap]

theorem kw_no3a_wdp_mprt_ydeCR_yToLoc_X_zero_mul (V : WeierstrassCurve.Projective R) :
    kw_no3a_wdp_mprt_ydeCR_yToLoc V (X 0)
        * algebraMap (MvPolynomial (Fin 3) R)
            (Localization.Away (X 1 : MvPolynomial (Fin 3) R)) (X 1)
      = algebraMap (MvPolynomial (Fin 3) R)
          (Localization.Away (X 1 : MvPolynomial (Fin 3) R)) (X 0) := by
  rw [kw_no3a_wdp_mprt_ydeCR_yToLoc_X_zero, Localization.mk_eq_mk'_apply]
  exact IsLocalization.mk'_spec _ (X 0 : MvPolynomial (Fin 3) R)
    (⟨X 1, 1, pow_one _⟩ : Submonoid.powers (X 1 : MvPolynomial (Fin 3) R))

theorem kw_no3a_wdp_mprt_ydeCR_yToLoc_X_two_mul (V : WeierstrassCurve.Projective R) :
    kw_no3a_wdp_mprt_ydeCR_yToLoc V (X 2)
        * algebraMap (MvPolynomial (Fin 3) R)
            (Localization.Away (X 1 : MvPolynomial (Fin 3) R)) (X 1)
      = algebraMap (MvPolynomial (Fin 3) R)
          (Localization.Away (X 1 : MvPolynomial (Fin 3) R)) (X 2) := by
  rw [kw_no3a_wdp_mprt_ydeCR_yToLoc_X_two, Localization.mk_eq_mk'_apply]
  exact IsLocalization.mk'_spec _ (X 2 : MvPolynomial (Fin 3) R)
    (⟨X 1, 1, pow_one _⟩ : Submonoid.powers (X 1 : MvPolynomial (Fin 3) R))

theorem kw_no3a_wdp_mprt_ydeCR_yToLoc_monomial (V : WeierstrassCurve.Projective R)
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

theorem kw_no3a_wdp_mprt_ydeCR_yToLoc_isHomogeneous (V : WeierstrassCurve.Projective R)
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

theorem kw_no3a_wdp_mprt_ydeCR_homog_comp_dehom (V : WeierstrassCurve.Projective R) :
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

def kw_no3a_wdp_mprt_ydeCR_yChartPolyEquiv (V : WeierstrassCurve.Projective R) :
    HomogeneousLocalization.Away (homogeneousSubmodule (Fin 3) R)
        (X 1 : MvPolynomial (Fin 3) R) ≃+* MvPolynomial (Fin 2) R :=
  RingEquiv.ofRingHom (kw_no3a_wdp_mprt_ydeCR_yChartAwayDehom (R := R))
    (kw_no3a_wdp_mprt_ydeCR_yHomog V)
    (kw_no3a_wdp_mprt_ydeCR_dehom_comp_homog V)
    (kw_no3a_wdp_mprt_ydeCR_homog_comp_dehom V)

theorem kw_no3a_wdp_mprt_ydeCR_yChartPolyEquiv_apply (V : WeierstrassCurve.Projective R)
    (z : HomogeneousLocalization.Away (homogeneousSubmodule (Fin 3) R)
      (X 1 : MvPolynomial (Fin 3) R)) :
    kw_no3a_wdp_mprt_ydeCR_yChartPolyEquiv V z
      = kw_no3a_wdp_mprt_ydeCR_yChartAwayDehom (R := R) z :=
  rfl

def kw_no3a_wdp_mprt_ydeCR_yAP (V : WeierstrassCurve.Projective R) :
    HomogeneousLocalization.Away (homogeneousSubmodule (Fin 3) R)
        (X 1 : MvPolynomial (Fin 3) R) →+* kw_no3a_wdp_mprt_ydeCR_coordRing V :=
  (Ideal.Quotient.mk _).comp (kw_no3a_wdp_mprt_ydeCR_yChartAwayDehom (R := R))

theorem kw_no3a_wdp_mprt_ydeCR_span_range_eq (V : WeierstrassCurve.Projective R) :
    Ideal.span (Set.range (fun _ : Fin 1 => kw_no3a_wdp_mprt_ydeCR_W_Y V))
      = Ideal.span {kw_no3a_wdp_mprt_ydeCR_W_Y V} := by
  congr 1
  exact Set.range_const

theorem kw_no3a_wdp_mprt_ydeCR_yAP_surjective (V : WeierstrassCurve.Projective R) :
    Function.Surjective (kw_no3a_wdp_mprt_ydeCR_yAP V) := by
  intro y
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective y
  exact ⟨(kw_no3a_wdp_mprt_ydeCR_yChartPolyEquiv V).symm p, by
    rw [kw_no3a_wdp_mprt_ydeCR_yAP, RingHom.comp_apply,
      ← kw_no3a_wdp_mprt_ydeCR_yChartPolyEquiv_apply, RingEquiv.apply_symm_apply]⟩

theorem kw_no3a_wdp_mprt_ydeCR_yChartAwayDehom_W_loc (V : WeierstrassCurve.Projective R) :
    kw_no3a_wdp_mprt_ydeCR_yChartAwayDehom (R := R) (kw_no3a_wdp_mprt_aqcCR_W_loc V 1)
      = kw_no3a_wdp_mprt_ydeCR_W_Y V := by
  unfold kw_no3a_wdp_mprt_aqcCR_W_loc
  rw [kw_no3a_wdp_mprt_ydeCR_yChartAwayDehom_awayMk, kw_no3a_wdp_mprt_ydeCR_dehomY_polynomial]

theorem kw_no3a_wdp_mprt_ydeCR_ker_yAP (V : WeierstrassCurve.Projective R) :
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

theorem kw_no3a_wdp_mprt_ydeCR_yAP_comp_ambientFromR (V : WeierstrassCurve.Projective R) :
    (kw_no3a_wdp_mprt_ydeCR_yAP V).comp (kw_no3a_wdp_mprt_aqcCR_ambientFromR V 1)
      = algebraMap R (kw_no3a_wdp_mprt_ydeCR_coordRing V) := by
  refine RingHom.ext fun r => ?_
  rw [kw_no3a_wdp_mprt_ydeCR_yAP, RingHom.comp_apply, RingHom.comp_apply,
    kw_no3a_wdp_mprt_ydeCR_yChartAwayDehom_const]
  rfl

end WeierstrassProjModel

end
end MEGA_KwNo3aWdpMprtYChartDehomEngineCR_lean
p2m_open "MvPolynomial HomogeneousLocalization HomogeneousIdealQuotientGrading WeierstrassProjModel P2MW.S_WeierstrassProjModel_exists_yChartAway_equiv_coordinateRing.WeierstrassProjModel P2MW.S_WeierstrassProjModel_exists_yChartAway_equiv_coordinateRing.ProjWeierstrassDehomog"

attribute [local instance] MvPolynomial.gradedAlgebra in

theorem solution
    {R : Type u} [CommRing R] (V : WeierstrassCurve.Projective R) :
    ∃ f : HomogeneousLocalization.Away (WeierstrassProjModel.projModelGradingCR V)
          (Ideal.Quotient.mk (WeierstrassProjModel.projModelHomogeneousIdealCR V).toIdeal
            (MvPolynomial.X 1 : MvPolynomial (Fin 3) R)) →+*
        (MvPolynomial (Fin 2) R ⧸ Ideal.span (Set.range fun _ : Fin 1 =>
          MvPolynomial.aeval
            (![MvPolynomial.X 0, 1, MvPolynomial.X 1] : Fin 3 → MvPolynomial (Fin 2) R) V.polynomial)),
      Function.Bijective f ∧
      f.comp ((HomogeneousLocalization.fromZeroRingHom (WeierstrassProjModel.projModelGradingCR V)
            (Submonoid.powers (Ideal.Quotient.mk
              (WeierstrassProjModel.projModelHomogeneousIdealCR V).toIdeal
              (MvPolynomial.X 1 : MvPolynomial (Fin 3) R)))).comp
          (algebraMap R (WeierstrassProjModel.projModelGradingCR V 0)))
        = algebraMap R (MvPolynomial (Fin 2) R ⧸ Ideal.span (Set.range fun _ : Fin 1 =>
            MvPolynomial.aeval
              (![MvPolynomial.X 0, 1, MvPolynomial.X 1] : Fin 3 → MvPolynomial (Fin 2) R)
              V.polynomial)) ∧
      ∀ (n : ℕ) (b : MvPolynomial (Fin 3) R)
        (hb : b ∈ MvPolynomial.homogeneousSubmodule (Fin 3) R (n • 1)),
        f (HomogeneousLocalization.Away.mk (WeierstrassProjModel.projModelGradingCR V)
            (HomogeneousIdealQuotientGrading.mk_mem_quotGradingSubmodule _ _
              ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr (MvPolynomial.isHomogeneous_X R 1)))
            n
            (Ideal.Quotient.mk (WeierstrassProjModel.projModelHomogeneousIdealCR V).toIdeal b)
            (HomogeneousIdealQuotientGrading.mk_mem_quotGradingSubmodule _ _ hb))
          = Ideal.Quotient.mk _
              (MvPolynomial.aeval
                (![MvPolynomial.X 0, 1, MvPolynomial.X 1] : Fin 3 → MvPolynomial (Fin 2) R) b) := by

  have hI : Ideal.span (Set.range (fun _ : Fin 1 => kw_no3a_wdp_mprt_ydeCR_W_Y V))
      = Ideal.span (Set.range fun _ : Fin 1 => MvPolynomial.aeval
          (![MvPolynomial.X 0, 1, MvPolynomial.X 1] : Fin 3 → MvPolynomial (Fin 2) R)
            V.polynomial) := by
    simp only [← kw_no3a_wdp_mprt_ydeCR_dehomY_polynomial]
    rfl
  have hker : RingHom.ker (kw_no3a_wdp_mprt_aqcCR_q V 1)
      = RingHom.ker (kw_no3a_wdp_mprt_ydeCR_yAP V) := by
    rw [kw_no3a_wdp_mprt_aqcCR_ker_q_eq_span, kw_no3a_wdp_mprt_ydeCR_ker_yAP]
  let g : HomogeneousLocalization.Away (projModelGradingCR V)
      (Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal (X 1 : MvPolynomial (Fin 3) R))
        →+* kw_no3a_wdp_mprt_ydeCR_coordRing V :=
    kw_no3a_wdp_mprt_aqcCR_liftOfSurjective
      (kw_no3a_wdp_mprt_aqcCR_q V 1) (kw_no3a_wdp_mprt_aqcCR_q_surjective V 1)
      (kw_no3a_wdp_mprt_ydeCR_yAP V) (le_of_eq hker)
  have hg : ∀ a, g (kw_no3a_wdp_mprt_aqcCR_q V 1 a) = kw_no3a_wdp_mprt_ydeCR_yAP V a :=
    kw_no3a_wdp_mprt_aqcCR_liftOfSurjective_apply _ _ _ _
  refine ⟨(Ideal.quotEquivOfEq hI).toRingHom.comp g, ?_, ?_, ?_⟩
  · exact (Ideal.quotEquivOfEq hI).bijective.comp
      (kw_no3a_wdp_mprt_aqcCR_liftOfSurjective_bijective (kw_no3a_wdp_mprt_aqcCR_q V 1)
        (kw_no3a_wdp_mprt_aqcCR_q_surjective V 1) (kw_no3a_wdp_mprt_ydeCR_yAP V)
        (kw_no3a_wdp_mprt_ydeCR_yAP_surjective V) hker)
  · refine RingHom.ext fun r => ?_
    have h := RingHom.congr_fun (kw_no3a_wdp_mprt_ydeCR_yAP_comp_ambientFromR V) r
    rw [RingHom.comp_apply] at h
    rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply,
      show (HomogeneousLocalization.fromZeroRingHom (projModelGradingCR V) _)
          (algebraMap R (projModelGradingCR V 0) r)
        = kw_no3a_wdp_mprt_aqcCR_q V 1 (kw_no3a_wdp_mprt_aqcCR_ambientFromR V 1 r) from
        (RingHom.congr_fun (kw_no3a_wdp_mprt_aqcCR_q_comp_ambientFromR V 1) r).symm,
      hg, h]
    show Ideal.quotEquivOfEq hI (Ideal.Quotient.mk _ (MvPolynomial.C r)) = _
    rw [Ideal.quotEquivOfEq_mk]
    rfl
  · intro n b hb
    have h := hg (HomogeneousLocalization.Away.mk (homogeneousSubmodule (Fin 3) R)
          (X_mem_homogeneousSubmodule_one R 1) n b hb)
    rw [kw_no3a_wdp_mprt_aqcCR_q_awayMk] at h
    rw [RingHom.comp_apply]
    refine (congrArg (Ideal.quotEquivOfEq hI).toRingHom h).trans ?_
    show Ideal.quotEquivOfEq hI (Ideal.Quotient.mk _
      (kw_no3a_wdp_mprt_ydeCR_yChartAwayDehom (R := R) _)) = _
    rw [kw_no3a_wdp_mprt_ydeCR_yChartAwayDehom_awayMk, Ideal.quotEquivOfEq_mk]
    rfl

end S_WeierstrassProjModel_exists_yChartAway_equiv_coordinateRing
end P2MW
export P2MW.S_WeierstrassProjModel_exists_yChartAway_equiv_coordinateRing (solution)
