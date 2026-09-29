-- Prove2me | solution 1 for WeierstrassProjModel.projModelStrCR_smooth_of_zChartBridge_of_yChartSmooth
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/be696244-cbf7-53f1-be23-696bd97098a4

import Definitions.Def_WeierstrassCurve_ProjModel
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.RingTheory.RingHom.Smooth
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.RingHom.LocallyStandardSmooth
import Mathlib.RingTheory.Smooth.StandardSmooth
import Mathlib.Algebra.MvPolynomial.PDeriv
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassProjModel_projModelStrCR_smooth_of_zChartBridge_of_yChartSmooth

set_option autoImplicit false
set_option Elab.async false

namespace HomogeneousIdealQuotientGrading
p2m_export "HomogeneousIdealQuotientGrading" "quotGrading quotGradingSubmodule mem_quotGradingSubmodule_iff mk_mem_quotGradingSubmodule decompose_quotGradingSubmodule_mk_apply"
p2m_open "HomogeneousIdealQuotientGrading"

section PolynomialDegreeZero

open MvPolynomial

private theorem mem_homogeneousSubmodule_zero_iff_exists_C {σ R : Type*} [CommSemiring R]
    {p : MvPolynomial σ R} :
    p ∈ homogeneousSubmodule σ R 0 ↔ ∃ r : R, C r = p := by
  constructor
  · intro hp
    rw [homogeneousSubmodule_zero] at hp
    obtain ⟨r, hr⟩ := Submodule.mem_one.mp hp
    exact ⟨r, by rwa [← algebraMap_eq]⟩
  · rintro ⟨r, rfl⟩
    exact (mem_homogeneousSubmodule _ _).mpr (isHomogeneous_C _ _)

end PolynomialDegreeZero

section ConstantCoeffKernel

open MvPolynomial

variable {σ R : Type*} [CommSemiring R]

private theorem constantCoeff_eq_zero_of_isHomogeneous_of_ne_zero {p : MvPolynomial σ R} {n : ℕ}
    (hp : p.IsHomogeneous n) (hn : n ≠ 0) :
    constantCoeff p = 0 :=
  hp.coeff_eq_zero (by simpa using hn.symm)

private theorem span_le_ker_constantCoeff_of_forall_constantCoeff_eq_zero
    {S : Set (MvPolynomial σ R)} (h : ∀ p ∈ S, constantCoeff p = 0) :
    Ideal.span S ≤ RingHom.ker (constantCoeff : MvPolynomial σ R →+* R) :=
  Ideal.span_le.mpr fun p hp => RingHom.mem_ker.mpr (h p hp)

private theorem span_le_ker_constantCoeff_of_forall_isHomogeneous_pos
    {S : Set (MvPolynomial σ R)} (h : ∀ p ∈ S, ∃ n : ℕ, n ≠ 0 ∧ p.IsHomogeneous n) :
    Ideal.span S ≤ RingHom.ker (constantCoeff : MvPolynomial σ R →+* R) :=
  span_le_ker_constantCoeff_of_forall_constantCoeff_eq_zero fun p hp => by
    obtain ⟨n, hn, hhom⟩ := h p hp
    exact constantCoeff_eq_zero_of_isHomogeneous_of_ne_zero hhom hn

end ConstantCoeffKernel

section DegreeZeroIdentification

open MvPolynomial

variable {σ R : Type*} [CommRing R]
variable (I : Ideal (MvPolynomial σ R))

private theorem quotGradingSubmodule_degreeZero_algebraMap_surjective :
    Function.Surjective
      (algebraMap R ((quotGradingSubmodule (homogeneousSubmodule σ R) I) 0)) := by
  rintro ⟨b, hb⟩
  obtain ⟨p, hp, rfl⟩ := (mem_quotGradingSubmodule_iff (homogeneousSubmodule σ R) I).mp hb
  obtain ⟨r, rfl⟩ := mem_homogeneousSubmodule_zero_iff_exists_C.mp hp
  exact ⟨r, Subtype.ext rfl⟩

private theorem quotGradingSubmodule_degreeZero_algebraMap_injective
    (hI : I ≤ RingHom.ker (constantCoeff : MvPolynomial σ R →+* R)) :
    Function.Injective
      (algebraMap R ((quotGradingSubmodule (homogeneousSubmodule σ R) I) 0)) := by
  intro r s hrs
  have hval : Ideal.Quotient.mk I (C r) = Ideal.Quotient.mk I (C s) :=
    congrArg Subtype.val hrs
  have hsub : (C r - C s : MvPolynomial σ R) ∈ I := Ideal.Quotient.eq.mp hval
  rw [← map_sub] at hsub
  have h0 : constantCoeff (C (r - s) : MvPolynomial σ R) = 0 := RingHom.mem_ker.mp (hI hsub)
  rw [constantCoeff_C] at h0
  exact sub_eq_zero.mp h0

private theorem quotGradingSubmodule_degreeZero_algebraMap_bijective
    (hI : I ≤ RingHom.ker (constantCoeff : MvPolynomial σ R →+* R)) :
    Function.Bijective
      (algebraMap R ((quotGradingSubmodule (homogeneousSubmodule σ R) I) 0)) :=
  ⟨quotGradingSubmodule_degreeZero_algebraMap_injective I hI,
   quotGradingSubmodule_degreeZero_algebraMap_surjective I⟩

end DegreeZeroIdentification

end HomogeneousIdealQuotientGrading

noncomputable section

p2m_open "AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousIdealQuotientGrading P2MW.S_WeierstrassProjModel_projModelStrCR_smooth_of_zChartBridge_of_yChartSmooth.HomogeneousIdealQuotientGrading"
open ProjWeierstrassCubicPrime HomogeneousLocalization

namespace WeierstrassProjModel
p2m_export "WeierstrassProjModel" "projModelHomogeneousIdealCR ProjModelRingCR projModelGradingCR projModelCR projModelStrCR"
p2m_open "WeierstrassProjModel"

attribute [local instance] MvPolynomial.gradedAlgebra

variable {R : Type} [CommRing R]

private theorem projModelIdeal_le_ker_constantCoeffCR (V : WeierstrassCurve.Projective R) :
    (projModelHomogeneousIdealCR V).toIdeal
      ≤ RingHom.ker (constantCoeff : MvPolynomial (Fin 3) R →+* R) :=
  span_le_ker_constantCoeff_of_forall_isHomogeneous_pos fun p hp => by
    rcases Set.mem_singleton_iff.mp hp with rfl
    exact ⟨3, by decide, isHomogeneous_polynomial V⟩

private theorem projModel_degreeZero_algebraMap_bijectiveCR (V : WeierstrassCurve.Projective R) :
    Function.Bijective (algebraMap R ((projModelGradingCR V) 0)) :=
  quotGradingSubmodule_degreeZero_algebraMap_bijective (projModelHomogeneousIdealCR V).toIdeal
    (projModelIdeal_le_ker_constantCoeffCR V)

private def projModelDegreeZeroRingEquivCR (V : WeierstrassCurve.Projective R) :
    R ≃+* ((projModelGradingCR V) 0) :=
  RingEquiv.ofBijective (algebraMap R ((projModelGradingCR V) 0))
    (projModel_degreeZero_algebraMap_bijectiveCR V)

private theorem kw_no3a_wdp_mprt_pmsCR_mk_X_mem_one
    (V : WeierstrassCurve.Projective R) (i : Fin 3) :
    Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal (X i : MvPolynomial (Fin 3) R)
      ∈ projModelGradingCR V 1 :=
  mk_mem_quotGradingSubmodule (homogeneousSubmodule (Fin 3) R)
    (projModelHomogeneousIdealCR V).toIdeal
    ((mem_homogeneousSubmodule _ _).mpr (isHomogeneous_X R i))

private theorem kw_no3a_wdp_mprt_pmsCR_ambient_irrelevant_le_span_X :
    (HomogeneousIdeal.irrelevant (homogeneousSubmodule (Fin 3) R)).toIdeal
      ≤ Ideal.span (Set.range (X : Fin 3 → MvPolynomial (Fin 3) R)) := by
  classical
  intro p hp
  rw [HomogeneousIdeal.toIdeal_irrelevant, RingHom.mem_ker] at hp
  have hzero : (DirectSum.decompose (homogeneousSubmodule (Fin 3) R) p 0
      : MvPolynomial (Fin 3) R) = 0 := by
    rw [← GradedRing.projZeroRingHom_apply]
    exact hp
  have hc0 : MvPolynomial.coeff 0 p = 0 := by
    conv_lhs => rw [← DirectSum.sum_support_decompose (homogeneousSubmodule (Fin 3) R) p]
    rw [MvPolynomial.coeff_sum]
    refine Finset.sum_eq_zero fun n _ => ?_
    by_cases h0 : n = 0
    · rw [h0, hzero, MvPolynomial.coeff_zero]
    · have hmem : ((DirectSum.decompose (homogeneousSubmodule (Fin 3) R) p n
          : MvPolynomial (Fin 3) R)).IsHomogeneous n :=
        (MvPolynomial.mem_homogeneousSubmodule _ _).mp (SetLike.coe_mem _)
      exact hmem.coeff_eq_zero (by simpa using Ne.symm h0)
  rw [← Set.image_univ, MvPolynomial.mem_ideal_span_X_image]
  intro m hm
  have hmne : m ≠ 0 := by
    rintro rfl; exact (MvPolynomial.mem_support_iff.mp hm) hc0
  obtain ⟨l, hl⟩ := Finsupp.ne_iff.mp hmne
  exact ⟨l, Set.mem_univ l, by simpa using hl⟩

private theorem kw_no3a_wdp_mprt_pmsCR_irrelevant_le_span_mk_X
    (V : WeierstrassCurve.Projective R) :
    (HomogeneousIdeal.irrelevant (projModelGradingCR V)).toIdeal
      ≤ Ideal.span (Set.range fun i : Fin 3 =>
          Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal
            (X i : MvPolynomial (Fin 3) R)) := by
  intro z hz
  rw [HomogeneousIdeal.toIdeal_irrelevant, RingHom.mem_ker,
    GradedRing.projZeroRingHom_apply] at hz
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
  rw [decompose_quotGradingSubmodule_mk_apply (homogeneousSubmodule (Fin 3) R)
      (projModelHomogeneousIdealCR V) p 0] at hz
  have hrewrite : Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal p
      = Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal
          (p - (DirectSum.decompose (homogeneousSubmodule (Fin 3) R) p 0
            : MvPolynomial (Fin 3) R)) := by
    rw [map_sub, hz, sub_zero]
  rw [hrewrite]
  have hirr : (p - (DirectSum.decompose (homogeneousSubmodule (Fin 3) R) p 0
        : MvPolynomial (Fin 3) R))
      ∈ (HomogeneousIdeal.irrelevant (homogeneousSubmodule (Fin 3) R)).toIdeal := by
    rw [HomogeneousIdeal.toIdeal_irrelevant, RingHom.mem_ker,
      GradedRing.projZeroRingHom_apply, DirectSum.decompose_sub,
      DirectSum.decompose_coe, DirectSum.sub_apply, DirectSum.of_eq_same,
      AddSubgroupClass.coe_sub, sub_self]
  have hmem := kw_no3a_wdp_mprt_pmsCR_ambient_irrelevant_le_span_X hirr
  have hmap : Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal
        (p - (DirectSum.decompose (homogeneousSubmodule (Fin 3) R) p 0
          : MvPolynomial (Fin 3) R))
      ∈ Ideal.map (Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal)
          (Ideal.span (Set.range (X : Fin 3 → MvPolynomial (Fin 3) R))) :=
    Ideal.mem_map_of_mem _ hmem
  rwa [Ideal.map_span, ← Set.range_comp] at hmap

private def kw_no3a_wdp_mprt_pmsCR_zCofactor (V : WeierstrassCurve.Projective R) :
    MvPolynomial (Fin 3) R :=
  X 1 ^ 2 + C V.a₁ * X 0 * X 1 + C V.a₃ * X 1 * X 2
    - C V.a₂ * X 0 ^ 2 - C V.a₄ * X 0 * X 2 - C V.a₆ * X 2 ^ 2

private theorem kw_no3a_wdp_mprt_pmsCR_polynomial_add_X0_cube
    (V : WeierstrassCurve.Projective R) :
    V.polynomial + X 0 ^ 3 = X 2 * kw_no3a_wdp_mprt_pmsCR_zCofactor V := by
  rw [WeierstrassCurve.Projective.polynomial, kw_no3a_wdp_mprt_pmsCR_zCofactor]
  ring

private theorem kw_no3a_wdp_mprt_pmsCR_mk_X0_cube_mem_span_mk_X2
    (V : WeierstrassCurve.Projective R) :
    (Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal
        (X 0 : MvPolynomial (Fin 3) R)) ^ 3
      ∈ Ideal.span {Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal
          (X 2 : MvPolynomial (Fin 3) R)} := by
  have hpoly : Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal V.polynomial = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  have hid := congrArg (Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal)
    (kw_no3a_wdp_mprt_pmsCR_polynomial_add_X0_cube V)
  rw [map_add, map_mul, map_pow, hpoly, zero_add] at hid
  rw [hid, Ideal.mem_span_singleton]
  exact ⟨_, rfl⟩

private theorem kw_no3a_wdp_mprt_pmsCR_not_both_in_ideal (V : WeierstrassCurve.Projective R)
    (x : Proj (projModelGradingCR V))
    (h1 : Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal
        (X 1 : MvPolynomial (Fin 3) R) ∈ x.asHomogeneousIdeal.toIdeal)
    (h2 : Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal
        (X 2 : MvPolynomial (Fin 3) R) ∈ x.asHomogeneousIdeal.toIdeal) :
    False := by
  have h0cube : (Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal
        (X 0 : MvPolynomial (Fin 3) R)) ^ 3 ∈ x.asHomogeneousIdeal.toIdeal :=
    (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr h2))
      (kw_no3a_wdp_mprt_pmsCR_mk_X0_cube_mem_span_mk_X2 V)
  have h0 : Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal
      (X 0 : MvPolynomial (Fin 3) R) ∈ x.asHomogeneousIdeal.toIdeal :=
    x.isPrime.mem_of_pow_mem 3 h0cube
  have hspan : Ideal.span (Set.range fun i : Fin 3 =>
        Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal
          (X i : MvPolynomial (Fin 3) R)) ≤ x.asHomogeneousIdeal.toIdeal := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
  exact x.not_irrelevant_le fun z hz =>
    hspan (kw_no3a_wdp_mprt_pmsCR_irrelevant_le_span_mk_X V hz)

private theorem kw_no3a_wdp_mprt_pmsCR_awayι_jointly_surjective
    (V : WeierstrassCurve.Projective R) (x : Proj (projModelGradingCR V)) :
    ∃ (i : Fin 2)
      (u : Spec (CommRingCat.of (HomogeneousLocalization.Away (projModelGradingCR V)
        (Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal
          (X (![1, 2] i) : MvPolynomial (Fin 3) R))))),
      (Proj.awayι (projModelGradingCR V) _
          (kw_no3a_wdp_mprt_pmsCR_mk_X_mem_one V (![1, 2] i)) Nat.one_pos) u = x := by
  by_cases hZ : Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal
      (X 2 : MvPolynomial (Fin 3) R) ∈ x.asHomogeneousIdeal.toIdeal
  · by_cases hY : Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal
        (X 1 : MvPolynomial (Fin 3) R) ∈ x.asHomogeneousIdeal.toIdeal
    · exact (kw_no3a_wdp_mprt_pmsCR_not_both_in_ideal V x hY hZ).elim
    · have hrange : x ∈ (Proj.awayι (projModelGradingCR V) _
          (kw_no3a_wdp_mprt_pmsCR_mk_X_mem_one V 1) Nat.one_pos).opensRange := by
        rw [Proj.opensRange_awayι]
        exact hY
      obtain ⟨u, hu⟩ := Scheme.Hom.mem_opensRange.mp hrange
      exact ⟨0, u, hu⟩
  · have hrange : x ∈ (Proj.awayι (projModelGradingCR V) _
        (kw_no3a_wdp_mprt_pmsCR_mk_X_mem_one V 2) Nat.one_pos).opensRange := by
      rw [Proj.opensRange_awayι]
      exact hZ
    obtain ⟨u, hu⟩ := Scheme.Hom.mem_opensRange.mp hrange
    exact ⟨1, u, hu⟩

private noncomputable def kw_no3a_wdp_mprt_pmsCR_openCover (V : WeierstrassCurve.Projective R) :
    (Proj (projModelGradingCR V)).OpenCover :=
  Scheme.Cover.mkOfCovers (Fin 2)
    (fun i => Spec (CommRingCat.of (HomogeneousLocalization.Away (projModelGradingCR V)
      (Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal
        (X (![1, 2] i) : MvPolynomial (Fin 3) R)))))
    (fun i => Proj.awayι (projModelGradingCR V) _
      (kw_no3a_wdp_mprt_pmsCR_mk_X_mem_one V (![1, 2] i)) Nat.one_pos)
    (kw_no3a_wdp_mprt_pmsCR_awayι_jointly_surjective V)

private abbrev KwNo3aWdpMprtProjModelYZChartSmoothCR
    (V : WeierstrassCurve.Projective R) : Prop :=
  RingHom.Smooth (HomogeneousLocalization.fromZeroRingHom (projModelGradingCR V)
    (Submonoid.powers (Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal
      (X 1 : MvPolynomial (Fin 3) R))))
  ∧ RingHom.Smooth (HomogeneousLocalization.fromZeroRingHom (projModelGradingCR V)
      (Submonoid.powers (Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal
        (X 2 : MvPolynomial (Fin 3) R))))

private theorem kw_no3a_wdp_mprt_pmsCR_smooth_toSpecZero (V : WeierstrassCurve.Projective R)
    (h : KwNo3aWdpMprtProjModelYZChartSmoothCR V) :
    Smooth (Proj.toSpecZero (projModelGradingCR V)) := by
  have hleg : ∀ i : Fin 2, Smooth (Proj.awayι (projModelGradingCR V)
      (Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal
        (X (![1, 2] i) : MvPolynomial (Fin 3) R))
      (kw_no3a_wdp_mprt_pmsCR_mk_X_mem_one V (![1, 2] i)) Nat.one_pos
      ≫ Proj.toSpecZero (projModelGradingCR V)) := by
    intro i
    rw [Proj.awayι_toSpecZero, HasRingHomProperty.Spec_iff (P := @AlgebraicGeometry.Smooth)]
    fin_cases i
    · exact h.1
    · exact h.2
  exact IsZariskiLocalAtSource.of_openCover (P := @AlgebraicGeometry.Smooth)
    (kw_no3a_wdp_mprt_pmsCR_openCover V) hleg

private theorem kw_no3a_wdp_mprt_pmsCR_ringHomSmooth_degreeZero
    (V : WeierstrassCurve.Projective R) :
    RingHom.Smooth (algebraMap R ((projModelGradingCR V) 0)) := by
  have hid : RingHom.Smooth (RingHom.id R) := by
    have hself : RingHom.Smooth (algebraMap R R) :=
      RingHom.smooth_algebraMap.mpr ⟨inferInstance, inferInstance⟩
    rwa [Algebra.algebraMap_self] at hself
  have h2 := RingHom.Smooth.respectsIso.1 (RingHom.id R)
    (projModelDegreeZeroRingEquivCR V) hid
  have key : ((projModelDegreeZeroRingEquivCR V).toRingHom).comp (RingHom.id R)
      = algebraMap R ((projModelGradingCR V) 0) :=
    RingHom.ext fun _ => rfl
  rwa [key] at h2

private theorem kw_no3a_wdp_mprt_pmsCR_smooth_degreeZero_leg
    (V : WeierstrassCurve.Projective R) :
    Smooth (Spec.map (CommRingCat.ofHom (algebraMap R ((projModelGradingCR V) 0)))) := by
  rw [HasRingHomProperty.Spec_iff (P := @AlgebraicGeometry.Smooth)]
  exact kw_no3a_wdp_mprt_pmsCR_ringHomSmooth_degreeZero V

private theorem kw_no3a_wdp_mprt_pmsCR_smooth_projModelStrCR
    (V : WeierstrassCurve.Projective R)
    (h : KwNo3aWdpMprtProjModelYZChartSmoothCR V) :
    Smooth (projModelStrCR V) := by
  haveI h1 := kw_no3a_wdp_mprt_pmsCR_smooth_toSpecZero V h
  haveI h2 := kw_no3a_wdp_mprt_pmsCR_smooth_degreeZero_leg V
  show Smooth (Proj.toSpecZero (projModelGradingCR V)
    ≫ Spec.map (CommRingCat.ofHom (algebraMap R ((projModelGradingCR V) 0))))
  infer_instance

end WeierstrassProjModel

end

noncomputable section

p2m_open "AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousIdealQuotientGrading P2MW.S_WeierstrassProjModel_projModelStrCR_smooth_of_zChartBridge_of_yChartSmooth.HomogeneousIdealQuotientGrading"
open ProjWeierstrassCubicPrime HomogeneousLocalization

namespace WeierstrassProjModel
p2m_export "WeierstrassProjModel" "projModelHomogeneousIdealCR ProjModelRingCR projModelGradingCR projModelCR projModelStrCR"
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

private theorem kw_no3a_wdp_mprt_zcdCR_ringHomSmooth_fromZero_of_fromR
    (V : WeierstrassCurve.Projective R) (i : Fin 3)
    (h : RingHom.Smooth (kw_no3a_wdp_mprt_zcdCR_fromR V i)) :
    RingHom.Smooth (HomogeneousLocalization.fromZeroRingHom (projModelGradingCR V)
      (Submonoid.powers (Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal
        (X i : MvPolynomial (Fin 3) R)))) := by
  have h2 := RingHom.Smooth.respectsIso.2 (kw_no3a_wdp_mprt_zcdCR_fromR V i)
    (projModelDegreeZeroRingEquivCR V).symm h
  have halg_eq : algebraMap R ((projModelGradingCR V) 0)
      = (projModelDegreeZeroRingEquivCR V).toRingHom := RingHom.ext fun _ => rfl
  have hinner : (algebraMap R ((projModelGradingCR V) 0)).comp
        (projModelDegreeZeroRingEquivCR V).symm.toRingHom
      = RingHom.id ((projModelGradingCR V) 0) := by
    rw [halg_eq]
    exact RingHom.ext fun x => (projModelDegreeZeroRingEquivCR V).apply_symm_apply x
  have key : (kw_no3a_wdp_mprt_zcdCR_fromR V i).comp
        (projModelDegreeZeroRingEquivCR V).symm.toRingHom
      = HomogeneousLocalization.fromZeroRingHom (projModelGradingCR V)
          (Submonoid.powers (Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal
            (X i : MvPolynomial (Fin 3) R))) := by
    unfold kw_no3a_wdp_mprt_zcdCR_fromR
    rw [RingHom.comp_assoc, hinner, RingHom.comp_id]
  rwa [key] at h2

private abbrev KwNo3aWdpMprtZChartAwayAffineCoordRingBridgeCR
    (V : WeierstrassCurve.Projective R) : Prop :=
  ∃ f : (HomogeneousLocalization.Away (projModelGradingCR V)
          (Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal
            (X 2 : MvPolynomial (Fin 3) R)))
        →+* (Polynomial (Polynomial R) ⧸ Ideal.span {V.toAffine.polynomial}),
    Function.Bijective f
    ∧ f.comp (kw_no3a_wdp_mprt_zcdCR_fromR V 2)
        = algebraMap R (Polynomial (Polynomial R) ⧸ Ideal.span {V.toAffine.polynomial})

private abbrev KwNo3aWdpMprtAffineWeierstrassCoordRingSmoothCR
    (V : WeierstrassCurve.Projective R) : Prop :=
  Algebra.Smooth R (Polynomial (Polynomial R) ⧸ Ideal.span {V.toAffine.polynomial})

private theorem kw_no3a_wdp_mprt_zcdCR_zChart_smooth_of_bridge_coordRing
    (V : WeierstrassCurve.Projective R)
    (hbr : KwNo3aWdpMprtZChartAwayAffineCoordRingBridgeCR V)
    (hcr : KwNo3aWdpMprtAffineWeierstrassCoordRingSmoothCR V) :
    RingHom.Smooth (HomogeneousLocalization.fromZeroRingHom (projModelGradingCR V)
      (Submonoid.powers (Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal
        (X 2 : MvPolynomial (Fin 3) R)))) := by
  obtain ⟨f, hbij, hecomp⟩ := hbr
  let e := RingEquiv.ofBijective f hbij
  have halg : RingHom.Smooth (algebraMap R
      (Polynomial (Polynomial R) ⧸ Ideal.span {V.toAffine.polynomial})) :=
    RingHom.smooth_algebraMap.mpr hcr
  have h3 := RingHom.Smooth.respectsIso.1 _ e.symm halg
  have hkey : e.symm.toRingHom.comp
        (algebraMap R (Polynomial (Polynomial R) ⧸ Ideal.span {V.toAffine.polynomial}))
      = kw_no3a_wdp_mprt_zcdCR_fromR V 2 := by
    rw [← hecomp]
    exact RingHom.ext fun x => e.symm_apply_apply _
  rw [hkey] at h3
  exact kw_no3a_wdp_mprt_zcdCR_ringHomSmooth_fromZero_of_fromR V 2 h3

private abbrev KwNo3aWdpMprtYChartFromRSmoothCR (V : WeierstrassCurve.Projective R) : Prop :=
  RingHom.Smooth (kw_no3a_wdp_mprt_zcdCR_fromR V 1)

private theorem kw_no3a_wdp_mprt_zcdCR_yzChartSmoothCR_of_bridge_coordRing_yFromR
    (V : WeierstrassCurve.Projective R)
    (hbr : KwNo3aWdpMprtZChartAwayAffineCoordRingBridgeCR V)
    (hcr : KwNo3aWdpMprtAffineWeierstrassCoordRingSmoothCR V)
    (hy : KwNo3aWdpMprtYChartFromRSmoothCR V) :
    KwNo3aWdpMprtProjModelYZChartSmoothCR V :=
  ⟨kw_no3a_wdp_mprt_zcdCR_ringHomSmooth_fromZero_of_fromR V 1 hy,
   kw_no3a_wdp_mprt_zcdCR_zChart_smooth_of_bridge_coordRing V hbr hcr⟩

private theorem kw_no3a_wdp_mprt_zcdCR_smooth_projModelStrCR_of_bridge_coordRing_yFromR
    (V : WeierstrassCurve.Projective R)
    (hbr : KwNo3aWdpMprtZChartAwayAffineCoordRingBridgeCR V)
    (hcr : KwNo3aWdpMprtAffineWeierstrassCoordRingSmoothCR V)
    (hy : KwNo3aWdpMprtYChartFromRSmoothCR V) :
    Smooth (projModelStrCR V) :=
  kw_no3a_wdp_mprt_pmsCR_smooth_projModelStrCR V
    (kw_no3a_wdp_mprt_zcdCR_yzChartSmoothCR_of_bridge_coordRing_yFromR V hbr hcr hy)

end WeierstrassProjModel

end

noncomputable section

open AlgebraicGeometry CategoryTheory ProjWeierstrassCubicPrime

namespace WeierstrassProjModel
p2m_export "WeierstrassProjModel" "projModelHomogeneousIdealCR ProjModelRingCR projModelGradingCR projModelCR projModelStrCR"
p2m_open "WeierstrassProjModel"

variable {R : Type} [CommRing R]

private def kw_no3a_wdp_mprt_acsCR_mkPartial (V : WeierstrassCurve.Projective R) (j : Fin 2) :
    Polynomial (Polynomial R) ⧸ Ideal.span {V.toAffine.polynomial} :=
  Ideal.Quotient.mk _ (![V.toAffine.polynomialX, V.toAffine.polynomialY] j)

private scoped instance kw_no3a_wdp_mprt_acsCR_finitePresentation_polyPoly :
    Algebra.FinitePresentation R (Polynomial (Polynomial R)) :=
  Algebra.FinitePresentation.trans R (Polynomial R) (Polynomial (Polynomial R))

private scoped instance kw_no3a_wdp_mprt_acsCR_finitePresentation (V : WeierstrassCurve.Projective R) :
    Algebra.FinitePresentation R
      (Polynomial (Polynomial R) ⧸ Ideal.span {V.toAffine.polynomial}) :=
  Algebra.FinitePresentation.quotient (Submodule.fg_span (Set.finite_singleton _))

private abbrev KwNo3aWdpMprtLocalizedPartialStandardSmoothCR
    (V : WeierstrassCurve.Projective R) : Prop :=
  ∀ j : Fin 2,
    Algebra.IsStandardSmooth R (Localization.Away (kw_no3a_wdp_mprt_acsCR_mkPartial V j))

private theorem kw_no3a_wdp_mprt_acsCR_smooth_of_partialsSpanTop_localizedStandardSmooth
    (V : WeierstrassCurve.Projective R)
    (hspan : Ideal.span (Set.range (kw_no3a_wdp_mprt_acsCR_mkPartial V)) = ⊤)
    (hleg : KwNo3aWdpMprtLocalizedPartialStandardSmoothCR V) :
    Algebra.Smooth R (Polynomial (Polynomial R) ⧸ Ideal.span {V.toAffine.polynomial}) := by
  rw [← RingHom.smooth_algebraMap, RingHom.smooth_iff_locally_isStandardSmooth]
  refine ⟨Set.range (kw_no3a_wdp_mprt_acsCR_mkPartial V), hspan, ?_⟩
  rintro t ⟨j, rfl⟩
  rw [← IsScalarTower.algebraMap_eq, RingHom.isStandardSmooth_algebraMap]
  exact hleg j

private abbrev KwNo3aWdpMprtAffinePartialsSpanTopCR
    (V : WeierstrassCurve.Projective R) : Prop :=
  Ideal.span (Set.range (kw_no3a_wdp_mprt_acsCR_mkPartial V)) = ⊤

private theorem kw_no3a_wdp_mprt_acsCR_affineCoordRingSmoothCR_of
    (V : WeierstrassCurve.Projective R)
    (hspan : KwNo3aWdpMprtAffinePartialsSpanTopCR V)
    (hleg : KwNo3aWdpMprtLocalizedPartialStandardSmoothCR V) :
    KwNo3aWdpMprtAffineWeierstrassCoordRingSmoothCR V :=
  kw_no3a_wdp_mprt_acsCR_smooth_of_partialsSpanTop_localizedStandardSmooth V hspan hleg

private theorem kw_no3a_wdp_mprt_acsCR_smooth_projModelStrCR_of_bridge_partials_yFromR
    (V : WeierstrassCurve.Projective R)
    (hbr : KwNo3aWdpMprtZChartAwayAffineCoordRingBridgeCR V)
    (hspan : KwNo3aWdpMprtAffinePartialsSpanTopCR V)
    (hleg : KwNo3aWdpMprtLocalizedPartialStandardSmoothCR V)
    (hy : KwNo3aWdpMprtYChartFromRSmoothCR V) :
    Smooth (projModelStrCR V) :=
  kw_no3a_wdp_mprt_zcdCR_smooth_projModelStrCR_of_bridge_coordRing_yFromR V hbr
    (kw_no3a_wdp_mprt_acsCR_affineCoordRingSmoothCR_of V hspan hleg) hy

end WeierstrassProjModel
p2m_reactivate "P2MW.S_WeierstrassProjModel_projModelStrCR_smooth_of_zChartBridge_of_yChartSmooth.WeierstrassProjModel"

end
p2m_reactivate "P2MW.S_WeierstrassProjModel_projModelStrCR_smooth_of_zChartBridge_of_yChartSmooth.WeierstrassProjModel"

noncomputable section

open AlgebraicGeometry CategoryTheory ProjWeierstrassCubicPrime
p2m_open "MvPolynomial Polynomial AlgebraicGeometry.Polynomial"

namespace WeierstrassProjModel
p2m_export "WeierstrassProjModel" "projModelHomogeneousIdealCR ProjModelRingCR projModelGradingCR projModelCR projModelStrCR"
p2m_open "WeierstrassProjModel"

variable {R : Type} [CommRing R]

private noncomputable def kw_no3a_wdp_mprt_spdCR_toIterated :
    MvPolynomial (Fin 2) R →ₐ[R] Polynomial (Polynomial R) :=
  MvPolynomial.aeval ![Polynomial.C Polynomial.X, Polynomial.X]

private noncomputable def kw_no3a_wdp_mprt_spdCR_fromIteratedRH :
    Polynomial (Polynomial R) →+* MvPolynomial (Fin 2) R :=
  Polynomial.eval₂RingHom (Polynomial.eval₂RingHom MvPolynomial.C (MvPolynomial.X 0))
    (MvPolynomial.X 1)

private theorem kw_no3a_wdp_mprt_spdCR_fromIterated_toIterated :
    (kw_no3a_wdp_mprt_spdCR_fromIteratedRH (R := R)).comp
        (kw_no3a_wdp_mprt_spdCR_toIterated (R := R)).toRingHom
      = RingHom.id (MvPolynomial (Fin 2) R) := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [kw_no3a_wdp_mprt_spdCR_fromIteratedRH, kw_no3a_wdp_mprt_spdCR_toIterated]
  · intro i
    fin_cases i <;>
      simp [kw_no3a_wdp_mprt_spdCR_fromIteratedRH, kw_no3a_wdp_mprt_spdCR_toIterated]

private theorem kw_no3a_wdp_mprt_spdCR_toIterated_fromIterated :
    (kw_no3a_wdp_mprt_spdCR_toIterated (R := R)).toRingHom.comp
        (kw_no3a_wdp_mprt_spdCR_fromIteratedRH (R := R))
      = RingHom.id (Polynomial (Polynomial R)) := by
  apply Polynomial.ringHom_ext'
  · apply Polynomial.ringHom_ext'
    · ext r
      simp [kw_no3a_wdp_mprt_spdCR_fromIteratedRH, kw_no3a_wdp_mprt_spdCR_toIterated]
    · simp [kw_no3a_wdp_mprt_spdCR_fromIteratedRH, kw_no3a_wdp_mprt_spdCR_toIterated]
  · simp [kw_no3a_wdp_mprt_spdCR_fromIteratedRH, kw_no3a_wdp_mprt_spdCR_toIterated]

private theorem kw_no3a_wdp_mprt_spdCR_toIterated_bijective :
    Function.Bijective (kw_no3a_wdp_mprt_spdCR_toIterated (R := R)) := by
  refine ⟨?_, ?_⟩
  · intro a b hab
    have := DFunLike.congr_fun (kw_no3a_wdp_mprt_spdCR_fromIterated_toIterated (R := R)) a
    have hb := DFunLike.congr_fun (kw_no3a_wdp_mprt_spdCR_fromIterated_toIterated (R := R)) b
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      RingHom.id_apply] at this hb
    rw [← this, ← hb, hab]
  · intro y
    refine ⟨kw_no3a_wdp_mprt_spdCR_fromIteratedRH y, ?_⟩
    have := DFunLike.congr_fun (kw_no3a_wdp_mprt_spdCR_toIterated_fromIterated (R := R)) y
    simpa [RingHom.comp_apply] using this

private noncomputable def kw_no3a_wdp_mprt_spdCR_bivariateEquiv :
    MvPolynomial (Fin 2) R ≃ₐ[R] Polynomial (Polynomial R) :=
  AlgEquiv.ofBijective (kw_no3a_wdp_mprt_spdCR_toIterated (R := R))
    (kw_no3a_wdp_mprt_spdCR_toIterated_bijective (R := R))

private noncomputable def kw_no3a_wdp_mprt_spdCR_W_mv (V : WeierstrassCurve.Projective R) :
    MvPolynomial (Fin 2) R :=
  (MvPolynomial.X 1) ^ 2
    + MvPolynomial.C V.toAffine.a₁ * MvPolynomial.X 0 * MvPolynomial.X 1
    + MvPolynomial.C V.toAffine.a₃ * MvPolynomial.X 1
    - ((MvPolynomial.X 0) ^ 3
        + MvPolynomial.C V.toAffine.a₂ * (MvPolynomial.X 0) ^ 2
        + MvPolynomial.C V.toAffine.a₄ * MvPolynomial.X 0
        + MvPolynomial.C V.toAffine.a₆)

private theorem kw_no3a_wdp_mprt_spdCR_algebraMap_polyPoly (r : R) :
    algebraMap R (Polynomial (Polynomial R)) r = Polynomial.C (Polynomial.C r) := by
  rw [IsScalarTower.algebraMap_apply R (Polynomial R) (Polynomial (Polynomial R)),
    Polynomial.algebraMap_eq, Polynomial.algebraMap_eq]

private theorem kw_no3a_wdp_mprt_spdCR_bivariateEquiv_W_mv (V : WeierstrassCurve.Projective R) :
    kw_no3a_wdp_mprt_spdCR_bivariateEquiv (R := R) (kw_no3a_wdp_mprt_spdCR_W_mv V)
      = V.toAffine.polynomial := by
  simp only [kw_no3a_wdp_mprt_spdCR_bivariateEquiv, AlgEquiv.ofBijective_apply,
    kw_no3a_wdp_mprt_spdCR_toIterated, kw_no3a_wdp_mprt_spdCR_W_mv,
    map_sub, map_add, map_mul, map_pow, MvPolynomial.aeval_X, MvPolynomial.aeval_C,
    WeierstrassCurve.Affine.polynomial, Matrix.cons_val_zero, Matrix.cons_val_one,
    kw_no3a_wdp_mprt_spdCR_algebraMap_polyPoly]
  ring

private theorem kw_no3a_wdp_mprt_spdCR_bivariateEquiv_pderiv0_W_mv
    (V : WeierstrassCurve.Projective R) :
    kw_no3a_wdp_mprt_spdCR_bivariateEquiv (R := R)
        (MvPolynomial.pderiv 0 (kw_no3a_wdp_mprt_spdCR_W_mv V))
      = V.toAffine.polynomialX := by
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  simp only [kw_no3a_wdp_mprt_spdCR_W_mv, map_sub, map_add, MvPolynomial.pderiv_mul,
    MvPolynomial.pderiv_pow, MvPolynomial.pderiv_C, MvPolynomial.pderiv_X_self,
    MvPolynomial.pderiv_X_of_ne h10, mul_zero, zero_mul, add_zero, zero_add, mul_one,
    kw_no3a_wdp_mprt_spdCR_bivariateEquiv, AlgEquiv.ofBijective_apply,
    kw_no3a_wdp_mprt_spdCR_toIterated, map_mul, map_pow, map_ofNat, map_natCast,
    MvPolynomial.aeval_X, MvPolynomial.aeval_C, WeierstrassCurve.Affine.polynomialX,
    Matrix.cons_val_zero, Matrix.cons_val_one, kw_no3a_wdp_mprt_spdCR_algebraMap_polyPoly]
  push_cast
  ring

private theorem kw_no3a_wdp_mprt_spdCR_bivariateEquiv_pderiv1_W_mv
    (V : WeierstrassCurve.Projective R) :
    kw_no3a_wdp_mprt_spdCR_bivariateEquiv (R := R)
        (MvPolynomial.pderiv 1 (kw_no3a_wdp_mprt_spdCR_W_mv V))
      = V.toAffine.polynomialY := by
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  simp only [kw_no3a_wdp_mprt_spdCR_W_mv, map_sub, map_add, MvPolynomial.pderiv_mul,
    MvPolynomial.pderiv_pow, MvPolynomial.pderiv_C, MvPolynomial.pderiv_X_self,
    MvPolynomial.pderiv_X_of_ne h01, mul_zero, zero_mul, add_zero, zero_add, mul_one,
    kw_no3a_wdp_mprt_spdCR_bivariateEquiv, AlgEquiv.ofBijective_apply,
    kw_no3a_wdp_mprt_spdCR_toIterated, map_mul, map_pow, map_ofNat, map_natCast, sub_zero,
    MvPolynomial.aeval_X, MvPolynomial.aeval_C, WeierstrassCurve.Affine.polynomialY,
    Matrix.cons_val_zero, Matrix.cons_val_one, kw_no3a_wdp_mprt_spdCR_algebraMap_polyPoly]
  push_cast
  ring

private theorem kw_no3a_wdp_mprt_spdCR_bivariateEquiv_pderiv_W_mv
    (V : WeierstrassCurve.Projective R) (j : Fin 2) :
    kw_no3a_wdp_mprt_spdCR_bivariateEquiv (R := R)
        (MvPolynomial.pderiv j (kw_no3a_wdp_mprt_spdCR_W_mv V))
      = ![V.toAffine.polynomialX, V.toAffine.polynomialY] j := by
  fin_cases j
  · exact kw_no3a_wdp_mprt_spdCR_bivariateEquiv_pderiv0_W_mv V
  · exact kw_no3a_wdp_mprt_spdCR_bivariateEquiv_pderiv1_W_mv V

private theorem kw_no3a_wdp_mprt_spdCR_span_map (V : WeierstrassCurve.Projective R) :
    Ideal.span {V.toAffine.polynomial}
      = (Ideal.span (Set.range (fun _ : Fin 1 => kw_no3a_wdp_mprt_spdCR_W_mv V))).map
          ((kw_no3a_wdp_mprt_spdCR_bivariateEquiv (R := R) :
            MvPolynomial (Fin 2) R →+* Polynomial (Polynomial R))) := by
  rw [Set.range_const, Ideal.map_span, Set.image_singleton]
  exact congrArg (fun z => Ideal.span {z})
    (kw_no3a_wdp_mprt_spdCR_bivariateEquiv_W_mv V).symm

private noncomputable def kw_no3a_wdp_mprt_spdCR_quotEquiv (V : WeierstrassCurve.Projective R) :
    (MvPolynomial (Fin 2) R
        ⧸ Ideal.span (Set.range (fun _ : Fin 1 => kw_no3a_wdp_mprt_spdCR_W_mv V)))
      ≃ₐ[R] (Polynomial (Polynomial R) ⧸ Ideal.span {V.toAffine.polynomial}) :=
  Ideal.quotientEquivAlg
    (Ideal.span (Set.range (fun _ : Fin 1 => kw_no3a_wdp_mprt_spdCR_W_mv V)))
    (Ideal.span {V.toAffine.polynomial})
    (kw_no3a_wdp_mprt_spdCR_bivariateEquiv (R := R))
    (kw_no3a_wdp_mprt_spdCR_span_map V)

private theorem kw_no3a_wdp_mprt_spdCR_quotEquiv_mk (V : WeierstrassCurve.Projective R)
    (p : MvPolynomial (Fin 2) R) :
    kw_no3a_wdp_mprt_spdCR_quotEquiv V (Ideal.Quotient.mk _ p)
      = Ideal.Quotient.mk _ (kw_no3a_wdp_mprt_spdCR_bivariateEquiv (R := R) p) :=
  rfl

private noncomputable def kw_no3a_wdp_mprt_spdCR_P₀ (V : WeierstrassCurve.Projective R) (j : Fin 2) :
    Algebra.PreSubmersivePresentation R
      (Polynomial (Polynomial R) ⧸ Ideal.span {V.toAffine.polynomial}) (Fin 2) (Fin 1) :=
  (Algebra.PreSubmersivePresentation.naive
    (v := fun _ : Fin 1 => kw_no3a_wdp_mprt_spdCR_W_mv V)
    (fun _ : Fin 1 => j) (Function.injective_of_subsingleton _)).ofAlgEquiv
    (kw_no3a_wdp_mprt_spdCR_quotEquiv V)

private theorem kw_no3a_wdp_mprt_spdCR_P₀_jacobian (V : WeierstrassCurve.Projective R) (j : Fin 2) :
    (kw_no3a_wdp_mprt_spdCR_P₀ V j).jacobian = kw_no3a_wdp_mprt_acsCR_mkPartial V j := by
  classical
  rw [kw_no3a_wdp_mprt_spdCR_P₀, Algebra.PreSubmersivePresentation.jacobian_ofAlgEquiv,
    Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det,
    Matrix.det_unique]
  simp only [Algebra.PreSubmersivePresentation.jacobiMatrix_naive, Fin.default_eq_zero]
  show kw_no3a_wdp_mprt_spdCR_quotEquiv V
      (Ideal.Quotient.mk _ (MvPolynomial.pderiv j (kw_no3a_wdp_mprt_spdCR_W_mv V)))
    = kw_no3a_wdp_mprt_acsCR_mkPartial V j
  rw [kw_no3a_wdp_mprt_spdCR_quotEquiv_mk,
    kw_no3a_wdp_mprt_spdCR_bivariateEquiv_pderiv_W_mv, kw_no3a_wdp_mprt_acsCR_mkPartial]

private noncomputable def kw_no3a_wdp_mprt_spdCR_compPres (V : WeierstrassCurve.Projective R)
    (j : Fin 2) :
    Algebra.PreSubmersivePresentation R
      (Localization.Away (kw_no3a_wdp_mprt_acsCR_mkPartial V j))
      (Unit ⊕ Fin 2) (Unit ⊕ Fin 1) :=
  (Algebra.PreSubmersivePresentation.localizationAway
    (Localization.Away (kw_no3a_wdp_mprt_acsCR_mkPartial V j))
    (kw_no3a_wdp_mprt_acsCR_mkPartial V j)).comp (kw_no3a_wdp_mprt_spdCR_P₀ V j)

private theorem kw_no3a_wdp_mprt_spdCR_compPres_jacobian_isUnit (V : WeierstrassCurve.Projective R)
    (j : Fin 2) :
    IsUnit (kw_no3a_wdp_mprt_spdCR_compPres V j).jacobian := by
  rw [kw_no3a_wdp_mprt_spdCR_compPres,
    Algebra.PreSubmersivePresentation.comp_jacobian_eq_jacobian_smul_jacobian,
    Algebra.PreSubmersivePresentation.localizationAway_jacobian,
    kw_no3a_wdp_mprt_spdCR_P₀_jacobian, Algebra.smul_def]
  exact (IsLocalization.Away.algebraMap_isUnit (kw_no3a_wdp_mprt_acsCR_mkPartial V j)).mul
    (IsLocalization.Away.algebraMap_isUnit (kw_no3a_wdp_mprt_acsCR_mkPartial V j))

private noncomputable def kw_no3a_wdp_mprt_spdCR_submersive (V : WeierstrassCurve.Projective R)
    (j : Fin 2) :
    Algebra.SubmersivePresentation R
      (Localization.Away (kw_no3a_wdp_mprt_acsCR_mkPartial V j))
      (Unit ⊕ Fin 2) (Unit ⊕ Fin 1) where
  __ := kw_no3a_wdp_mprt_spdCR_compPres V j
  jacobian_isUnit := kw_no3a_wdp_mprt_spdCR_compPres_jacobian_isUnit V j

private theorem kw_no3a_wdp_mprt_spdCR_localizedPartialStandardSmoothCR
    (V : WeierstrassCurve.Projective R) :
    KwNo3aWdpMprtLocalizedPartialStandardSmoothCR V :=
  fun j => (kw_no3a_wdp_mprt_spdCR_submersive V j).isStandardSmooth

private theorem kw_no3a_wdp_mprt_spdCR_smooth_projModelStrCR_of_bridge_partialsSpan_yFromR
    (V : WeierstrassCurve.Projective R)
    (hbr : KwNo3aWdpMprtZChartAwayAffineCoordRingBridgeCR V)
    (hspan : KwNo3aWdpMprtAffinePartialsSpanTopCR V)
    (hy : KwNo3aWdpMprtYChartFromRSmoothCR V) :
    Smooth (projModelStrCR V) :=
  kw_no3a_wdp_mprt_acsCR_smooth_projModelStrCR_of_bridge_partials_yFromR V hbr hspan
    (kw_no3a_wdp_mprt_spdCR_localizedPartialStandardSmoothCR V) hy

end WeierstrassProjModel
p2m_reactivate "P2MW.S_WeierstrassProjModel_projModelStrCR_smooth_of_zChartBridge_of_yChartSmooth.WeierstrassProjModel"

end
p2m_reactivate "P2MW.S_WeierstrassProjModel_projModelStrCR_smooth_of_zChartBridge_of_yChartSmooth.WeierstrassProjModel"

noncomputable section

open AlgebraicGeometry CategoryTheory ProjWeierstrassCubicPrime
p2m_open "Polynomial AlgebraicGeometry.Polynomial WeierstrassCurve"

namespace WeierstrassProjModel
p2m_export "WeierstrassProjModel" "projModelHomogeneousIdealCR ProjModelRingCR projModelGradingCR projModelCR projModelStrCR"
p2m_open "WeierstrassProjModel"

variable {R : Type} [CommRing R]

private theorem kw_no3a_wdp_mprt_pstCR_algHom_eq_evalEval_map {L : Type*} [CommRing L] [Algebra R L]
    (π : Polynomial (Polynomial R) →ₐ[R] L) (p : Polynomial (Polynomial R)) :
    π p = (p.map (Polynomial.mapRingHom (algebraMap R L))).evalEval
      (π (Polynomial.C Polynomial.X)) (π Polynomial.X) := by
  have hrh :
      (π : Polynomial (Polynomial R) →+* L)
        = (Polynomial.evalEvalRingHom (π (Polynomial.C Polynomial.X)) (π Polynomial.X)).comp
            (Polynomial.mapRingHom (Polynomial.mapRingHom (algebraMap R L))) := by
    apply Polynomial.ringHom_ext'
    · apply Polynomial.ringHom_ext'
      · ext r
        have hπr : π (Polynomial.C (Polynomial.C r)) = algebraMap R L r := by
          rw [← kw_no3a_wdp_mprt_spdCR_algebraMap_polyPoly r]; exact π.commutes r
        simp [hπr]
      · simp
    · simp
  exact DFunLike.congr_fun hrh p

private theorem kw_no3a_wdp_mprt_pstCR_algHom_polynomial {L : Type*} [CommRing L] [Algebra R L]
    (π : Polynomial (Polynomial R) →ₐ[R] L) (V : WeierstrassCurve.Projective R) :
    π V.toAffine.polynomial
      = (V.toAffine.map (algebraMap R L)).polynomial.evalEval
          (π (Polynomial.C Polynomial.X)) (π Polynomial.X) := by
  rw [kw_no3a_wdp_mprt_pstCR_algHom_eq_evalEval_map π,
    ← WeierstrassCurve.Affine.map_polynomial]

private theorem kw_no3a_wdp_mprt_pstCR_algHom_polynomialX {L : Type*} [CommRing L] [Algebra R L]
    (π : Polynomial (Polynomial R) →ₐ[R] L) (V : WeierstrassCurve.Projective R) :
    π V.toAffine.polynomialX
      = (V.toAffine.map (algebraMap R L)).polynomialX.evalEval
          (π (Polynomial.C Polynomial.X)) (π Polynomial.X) := by
  rw [kw_no3a_wdp_mprt_pstCR_algHom_eq_evalEval_map π,
    ← WeierstrassCurve.Affine.map_polynomialX]

private theorem kw_no3a_wdp_mprt_pstCR_algHom_polynomialY {L : Type*} [CommRing L] [Algebra R L]
    (π : Polynomial (Polynomial R) →ₐ[R] L) (V : WeierstrassCurve.Projective R) :
    π V.toAffine.polynomialY
      = (V.toAffine.map (algebraMap R L)).polynomialY.evalEval
          (π (Polynomial.C Polynomial.X)) (π Polynomial.X) := by
  rw [kw_no3a_wdp_mprt_pstCR_algHom_eq_evalEval_map π,
    ← WeierstrassCurve.Affine.map_polynomialY]

private theorem kw_no3a_wdp_mprt_pstCR_no_maximal_over_triple
    (V : WeierstrassCurve.Projective R) [V.IsElliptic]
    (M : Ideal (Polynomial (Polynomial R))) (hmax : M.IsMaximal)
    (hW : V.toAffine.polynomial ∈ M) (hX : V.toAffine.polynomialX ∈ M)
    (hY : V.toAffine.polynomialY ∈ M) :
    False := by
  classical
  haveI : Nontrivial (Polynomial (Polynomial R) ⧸ M) :=
    Ideal.Quotient.nontrivial_iff.mpr hmax.ne_top

  have hπW : (Ideal.Quotient.mkₐ R M) V.toAffine.polynomial = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hW
  have hπX : (Ideal.Quotient.mkₐ R M) V.toAffine.polynomialX = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hX
  have hπY : (Ideal.Quotient.mkₐ R M) V.toAffine.polynomialY = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hY

  have hEq : (V.toAffine.map (algebraMap R (Polynomial (Polynomial R) ⧸ M))).Equation
      ((Ideal.Quotient.mkₐ R M) (Polynomial.C Polynomial.X))
      ((Ideal.Quotient.mkₐ R M) Polynomial.X) := by
    have h := @kw_no3a_wdp_mprt_pstCR_algHom_polynomial R _ (Polynomial (Polynomial R) ⧸ M)
      inferInstance inferInstance (Ideal.Quotient.mkₐ R M) V
    rw [hπW] at h
    exact h.symm
  have hX0 : (V.toAffine.map (algebraMap R
      (Polynomial (Polynomial R) ⧸ M))).polynomialX.evalEval
      ((Ideal.Quotient.mkₐ R M) (Polynomial.C Polynomial.X))
      ((Ideal.Quotient.mkₐ R M) Polynomial.X) = 0 := by
    have h := @kw_no3a_wdp_mprt_pstCR_algHom_polynomialX R _ (Polynomial (Polynomial R) ⧸ M)
      inferInstance inferInstance (Ideal.Quotient.mkₐ R M) V
    rw [hπX] at h
    exact h.symm
  have hY0 : (V.toAffine.map (algebraMap R
      (Polynomial (Polynomial R) ⧸ M))).polynomialY.evalEval
      ((Ideal.Quotient.mkₐ R M) (Polynomial.C Polynomial.X))
      ((Ideal.Quotient.mkₐ R M) Polynomial.X) = 0 := by
    have h := @kw_no3a_wdp_mprt_pstCR_algHom_polynomialY R _ (Polynomial (Polynomial R) ⧸ M)
      inferInstance inferInstance (Ideal.Quotient.mkₐ R M) V
    rw [hπY] at h
    exact h.symm

  rcases ((WeierstrassCurve.Affine.equation_iff_nonsingular).mp hEq).2 with h | h
  · exact h hX0
  · exact h hY0

private theorem kw_no3a_wdp_mprt_pstCR_affinePartialsSpanTopCR
    (V : WeierstrassCurve.Projective R) [V.IsElliptic] :
    KwNo3aWdpMprtAffinePartialsSpanTopCR V := by
  classical
  by_contra hne
  obtain ⟨m, hmax, hle⟩ :=
    Ideal.exists_le_maximal (Ideal.span (Set.range (kw_no3a_wdp_mprt_acsCR_mkPartial V))) hne

  let M : Ideal (Polynomial (Polynomial R)) :=
    Ideal.comap (Ideal.Quotient.mk (Ideal.span {V.toAffine.polynomial})) m
  have hMmax : M.IsMaximal :=
    Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
  have hWM : V.toAffine.polynomial ∈ M := by
    simp only [M, Ideal.mem_comap,
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)]
    exact Submodule.zero_mem m
  have hXM : V.toAffine.polynomialX ∈ M := by
    have h0 : kw_no3a_wdp_mprt_acsCR_mkPartial V 0 ∈ m := hle (Ideal.subset_span ⟨0, rfl⟩)
    simpa only [kw_no3a_wdp_mprt_acsCR_mkPartial, Matrix.cons_val_zero, M,
      Ideal.mem_comap] using h0
  have hYM : V.toAffine.polynomialY ∈ M := by
    have h1 : kw_no3a_wdp_mprt_acsCR_mkPartial V 1 ∈ m := hle (Ideal.subset_span ⟨1, rfl⟩)
    simp only [kw_no3a_wdp_mprt_acsCR_mkPartial, Matrix.cons_val_one, Matrix.head_cons,
      M, Ideal.mem_comap] at h1
    exact h1
  exact kw_no3a_wdp_mprt_pstCR_no_maximal_over_triple V M hMmax hWM hXM hYM

private theorem kw_no3a_wdp_mprt_pstCR_smooth_projModelStrCR_of_bridge_yFromR
    (V : WeierstrassCurve.Projective R) [V.IsElliptic]
    (hbr : KwNo3aWdpMprtZChartAwayAffineCoordRingBridgeCR V)
    (hy : KwNo3aWdpMprtYChartFromRSmoothCR V) :
    Smooth (projModelStrCR V) :=
  kw_no3a_wdp_mprt_spdCR_smooth_projModelStrCR_of_bridge_partialsSpan_yFromR V hbr
    (kw_no3a_wdp_mprt_pstCR_affinePartialsSpanTopCR V) hy

end WeierstrassProjModel
p2m_reactivate "P2MW.S_WeierstrassProjModel_projModelStrCR_smooth_of_zChartBridge_of_yChartSmooth.WeierstrassProjModel"

end
p2m_reactivate "P2MW.S_WeierstrassProjModel_projModelStrCR_smooth_of_zChartBridge_of_yChartSmooth.WeierstrassProjModel"

attribute [local instance] MvPolynomial.gradedAlgebra in
theorem solution
    {R : Type} [CommRing R] (V : WeierstrassCurve.Projective R) [V.IsElliptic]
    (hbr : ∃ f : HomogeneousLocalization.Away (WeierstrassProjModel.projModelGradingCR V)
          (Ideal.Quotient.mk (WeierstrassProjModel.projModelHomogeneousIdealCR V).toIdeal
            (MvPolynomial.X 2 : MvPolynomial (Fin 3) R)) →+*
        (Polynomial (Polynomial R) ⧸ Ideal.span {V.toAffine.polynomial}),
      Function.Bijective f ∧
        f.comp ((HomogeneousLocalization.fromZeroRingHom
              (WeierstrassProjModel.projModelGradingCR V)
              (Submonoid.powers (Ideal.Quotient.mk
                (WeierstrassProjModel.projModelHomogeneousIdealCR V).toIdeal
                (MvPolynomial.X 2 : MvPolynomial (Fin 3) R)))).comp
            (algebraMap R (WeierstrassProjModel.projModelGradingCR V 0))) =
          algebraMap R (Polynomial (Polynomial R) ⧸ Ideal.span {V.toAffine.polynomial}))
    (hy : RingHom.Smooth ((HomogeneousLocalization.fromZeroRingHom
            (WeierstrassProjModel.projModelGradingCR V)
            (Submonoid.powers (Ideal.Quotient.mk
              (WeierstrassProjModel.projModelHomogeneousIdealCR V).toIdeal
              (MvPolynomial.X 1 : MvPolynomial (Fin 3) R)))).comp
          (algebraMap R (WeierstrassProjModel.projModelGradingCR V 0)))) :
    AlgebraicGeometry.Smooth (WeierstrassProjModel.projModelStrCR V) :=
  WeierstrassProjModel.kw_no3a_wdp_mprt_pstCR_smooth_projModelStrCR_of_bridge_yFromR V hbr hy

end S_WeierstrassProjModel_projModelStrCR_smooth_of_zChartBridge_of_yChartSmooth
end P2MW
export P2MW.S_WeierstrassProjModel_projModelStrCR_smooth_of_zChartBridge_of_yChartSmooth (solution)
