-- Prove2me | solution 1 for WeierstrassProjModel.kw_bc_baseChangeIso
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/872e31de-f304-5188-8267-c801f9447614

import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Theorems.Thm_WeierstrassProjModel_kw_bc_awayIsPushoutAll
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.RingTheory.RingHom.Smooth
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassProjModel_kw_bc_baseChangeIso

set_option autoImplicit false
set_option Elab.async false

section MEGA_prelude_bc_lean

end MEGA_prelude_bc_lean

section MEGA_KwNo3aWdpMprtProjModelSmoothCRDischarge_lean

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousIdealQuotientGrading
open ProjWeierstrassCubicPrime HomogeneousLocalization

namespace WeierstrassProjModel
p2m_export "WeierstrassProjModel" "projModelHomogeneousIdealCR projModelHomogeneousIdealCR_toIdeal ProjModelRingCR projModelGradingCR projModelCR projModelStrCR kw_pbac_mk_X_mem_one_CR kw_bc_awayIsPushoutAll"
p2m_open "WeierstrassProjModel"

attribute [local instance] MvPolynomial.gradedAlgebra

variable {R : Type} [CommRing R]

theorem kw_no3a_wdp_mprt_pmsCR_mk_X_mem_one
    (V : WeierstrassCurve.Projective R) (i : Fin 3) :
    Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal (X i : MvPolynomial (Fin 3) R)
      ∈ projModelGradingCR V 1 :=
  mk_mem_quotGradingSubmodule (homogeneousSubmodule (Fin 3) R)
    (projModelHomogeneousIdealCR V).toIdeal
    ((mem_homogeneousSubmodule _ _).mpr (isHomogeneous_X R i))

theorem kw_no3a_wdp_mprt_pmsCR_ambient_irrelevant_le_span_X :
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

theorem kw_no3a_wdp_mprt_pmsCR_irrelevant_le_span_mk_X
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

def kw_no3a_wdp_mprt_pmsCR_zCofactor (V : WeierstrassCurve.Projective R) :
    MvPolynomial (Fin 3) R :=
  X 1 ^ 2 + C V.a₁ * X 0 * X 1 + C V.a₃ * X 1 * X 2
    - C V.a₂ * X 0 ^ 2 - C V.a₄ * X 0 * X 2 - C V.a₆ * X 2 ^ 2

theorem kw_no3a_wdp_mprt_pmsCR_polynomial_add_X0_cube
    (V : WeierstrassCurve.Projective R) :
    V.polynomial + X 0 ^ 3 = X 2 * kw_no3a_wdp_mprt_pmsCR_zCofactor V := by
  rw [WeierstrassCurve.Projective.polynomial, kw_no3a_wdp_mprt_pmsCR_zCofactor]
  ring

theorem kw_no3a_wdp_mprt_pmsCR_mk_X0_cube_mem_span_mk_X2
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

theorem kw_no3a_wdp_mprt_pmsCR_not_both_in_ideal (V : WeierstrassCurve.Projective R)
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

theorem kw_no3a_wdp_mprt_pmsCR_awayι_jointly_surjective
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

noncomputable def kw_no3a_wdp_mprt_pmsCR_openCover (V : WeierstrassCurve.Projective R) :
    (Proj (projModelGradingCR V)).OpenCover :=
  Scheme.Cover.mkOfCovers (Fin 2)
    (fun i => Spec (CommRingCat.of (HomogeneousLocalization.Away (projModelGradingCR V)
      (Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal
        (X (![1, 2] i) : MvPolynomial (Fin 3) R)))))
    (fun i => Proj.awayι (projModelGradingCR V) _
      (kw_no3a_wdp_mprt_pmsCR_mk_X_mem_one V (![1, 2] i)) Nat.one_pos)
    (kw_no3a_wdp_mprt_pmsCR_awayι_jointly_surjective V)

end WeierstrassProjModel

end

end MEGA_KwNo3aWdpMprtProjModelSmoothCRDischarge_lean

section MEGA_KwProjModelCRBaseChangeDischarge_lean

set_option autoImplicit false
set_option maxHeartbeats 12800000
set_option synthInstance.maxHeartbeats 1600000

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits WeierstrassCurve
open MvPolynomial HomogeneousLocalization HomogeneousIdealQuotientGrading

namespace WeierstrassProjModel
p2m_export "WeierstrassProjModel" "projModelHomogeneousIdealCR projModelHomogeneousIdealCR_toIdeal ProjModelRingCR projModelGradingCR projModelCR projModelStrCR kw_pbac_mk_X_mem_one_CR kw_bc_awayIsPushoutAll"
p2m_open "WeierstrassProjModel"

attribute [local instance] MvPolynomial.gradedAlgebra

section GradedHom

variable {R : Type} [CommRing R] (W : WeierstrassCurve R)
variable (K : Type) [CommRing K] [Algebra R K]

local notation3 "φ" => algebraMap R K
local notation3 "W_K" => (W.map (algebraMap R K)).toProjective

theorem kw_pmbc_map_span_polynomial :
    (Ideal.span {W.toProjective.polynomial}).map (MvPolynomial.map φ)
      = Ideal.span {(W_K).polynomial} := by
  rw [Ideal.map_span, Set.image_singleton, WeierstrassCurve.Projective.map_polynomial]

theorem kw_pmbc_le_comap :
    (projModelHomogeneousIdealCR W.toProjective).toIdeal
      ≤ Ideal.comap (MvPolynomial.map φ) (projModelHomogeneousIdealCR W_K).toIdeal := by
  rw [projModelHomogeneousIdealCR_toIdeal, projModelHomogeneousIdealCR_toIdeal,
    ← kw_pmbc_map_span_polynomial W K]
  exact Ideal.le_comap_map

def kw_pmbc_gradedRingHom :
    (projModelGradingCR W.toProjective) →+*ᵍ (projModelGradingCR W_K) where
  toRingHom := Ideal.quotientMap _ (MvPolynomial.map φ) (kw_pmbc_le_comap W K)
  map_mem := by
    rintro n _ ⟨p, hp, rfl⟩
    exact mk_mem_quotGradingSubmodule _ _
      ((mem_homogeneousSubmodule _ _).mpr (((mem_homogeneousSubmodule _ _).mp hp).map φ))

theorem kw_pmbc_gradedRingHom_mk_X (i : Fin 3) :
    kw_pmbc_gradedRingHom W K
        (Ideal.Quotient.mk _ (X i : MvPolynomial (Fin 3) R))
      = Ideal.Quotient.mk _ (X i : MvPolynomial (Fin 3) K) := by
  show Ideal.quotientMap _ (MvPolynomial.map φ) (kw_pmbc_le_comap W K)
    (Ideal.Quotient.mk _ (X i : MvPolynomial (Fin 3) R)) = _
  rw [Ideal.quotientMap_mk, MvPolynomial.map_X]

theorem kw_pmbc_irrelevant_le :
    HomogeneousIdeal.irrelevant (projModelGradingCR W_K)
      ≤ (HomogeneousIdeal.irrelevant (projModelGradingCR W.toProjective)).map
          (kw_pmbc_gradedRingHom W K) := by
  intro x hx
  have hspan : x ∈ (Ideal.span (Set.range fun i : Fin 3 =>
      Ideal.Quotient.mk _ (X i : MvPolynomial (Fin 3) K))) :=
    kw_no3a_wdp_mprt_pmsCR_irrelevant_le_span_mk_X W_K hx
  refine (Ideal.span_le.mpr ?_) hspan
  rintro _ ⟨i, rfl⟩
  show Ideal.Quotient.mk _ (X i : MvPolynomial (Fin 3) K)
    ∈ (HomogeneousIdeal.map (kw_pmbc_gradedRingHom W K)
        (HomogeneousIdeal.irrelevant (projModelGradingCR W.toProjective)))
  rw [← kw_pmbc_gradedRingHom_mk_X W K i, ← HomogeneousIdeal.mem_iff,
    HomogeneousIdeal.toIdeal_map]
  exact Ideal.mem_map_of_mem _ (HomogeneousIdeal.mem_irrelevant_of_mem _ one_pos
    (kw_pbac_mk_X_mem_one_CR R W.toProjective i))

def kw_pmbc_projModelMap : projModelCR W_K ⟶ projModelCR W.toProjective :=
  Proj.map (kw_pmbc_gradedRingHom W K) (kw_pmbc_irrelevant_le W K)

end GradedHom

section IsPullback

variable {R : Type} [CommRing R] (W : WeierstrassCurve R)
variable (K : Type) [CommRing K] [Algebra R K]

local notation3 "φ" => algebraMap R K
local notation3 "W_K" => (W.map (algebraMap R K)).toProjective
local notation3 "ℬ_R" => projModelGradingCR W.toProjective
local notation3 "ℬ_K" => projModelGradingCR W_K
local notation3 "mkX_R" i =>
  Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
    (X i : MvPolynomial (Fin 3) R)
local notation3 "mkX_K" i =>
  Ideal.Quotient.mk (projModelHomogeneousIdealCR W_K).toIdeal
    (X i : MvPolynomial (Fin 3) K)

def kw_pmbc_awayAlgMapR (i : Fin 3) : R →+* Away ℬ_R (mkX_R i) :=
  (fromZeroRingHom ℬ_R _).comp (algebraMap R ↥(ℬ_R 0))

theorem kw_pmbc_awayAlgMapR_val (i : Fin 3) (r : R) :
    (kw_pmbc_awayAlgMapR W i r).val = Localization.mk (Ideal.Quotient.mk _ (C r)) 1 := by
  show Localization.mk _ _ = _
  rfl

noncomputable scoped instance kw_pmbc_awayAlgR (i : Fin 3) : Algebra R (Away ℬ_R (mkX_R i)) where
  algebraMap := kw_pmbc_awayAlgMapR W i
  commutes' _ _ := mul_comm _ _
  smul_def' r a := HomogeneousLocalization.val_injective _ <| by
    rw [HomogeneousLocalization.val_smul, HomogeneousLocalization.val_mul,
      kw_pmbc_awayAlgMapR_val, Localization.mk_one_eq_algebraMap, ← Algebra.smul_def]
    exact (algebraMap_smul (ProjModelRingCR W.toProjective) r a.val).symm

def kw_pmbc_awayAlgMapK (i : Fin 3) :
    K →+* Away ℬ_K ((kw_pmbc_gradedRingHom W K) (mkX_R i)) :=
  (fromZeroRingHom ℬ_K _).comp (algebraMap K ↥(ℬ_K 0))

theorem kw_pmbc_awayAlgMapK_val (i : Fin 3) (s : K) :
    (kw_pmbc_awayAlgMapK W K i s).val = Localization.mk (Ideal.Quotient.mk _ (C s)) 1 := by
  show Localization.mk _ _ = _
  rfl

noncomputable scoped instance kw_pmbc_awayAlgK (i : Fin 3) :
    Algebra K (Away ℬ_K ((kw_pmbc_gradedRingHom W K) (mkX_R i))) where
  algebraMap := kw_pmbc_awayAlgMapK W K i
  commutes' _ _ := mul_comm _ _
  smul_def' s a := HomogeneousLocalization.val_injective _ <| by
    rw [HomogeneousLocalization.val_smul, HomogeneousLocalization.val_mul,
      kw_pmbc_awayAlgMapK_val, Localization.mk_one_eq_algebraMap, ← Algebra.smul_def]
    exact (algebraMap_smul (ProjModelRingCR W_K) s a.val).symm

noncomputable scoped instance kw_pmbc_awayMapAlgebra (i : Fin 3) :
    Algebra (Away ℬ_R (mkX_R i)) (Away ℬ_K ((kw_pmbc_gradedRingHom W K) (mkX_R i))) :=
  (Away.map (kw_pmbc_gradedRingHom W K) (mkX_R i)).toAlgebra

theorem kw_pmbc_awayMap_fromZero (i : Fin 3) (r : R) :
    Away.map (kw_pmbc_gradedRingHom W K) (mkX_R i) (kw_pmbc_awayAlgMapR W i r)
      = kw_pmbc_awayAlgMapK W K i (φ r) := by
  apply HomogeneousLocalization.val_injective
  show Localization.mk _ _ = Localization.mk _ _
  refine congrArg₂ Localization.mk ?_ (Subtype.ext (map_one _))
  show Ideal.quotientMap _ (MvPolynomial.map φ) (kw_pmbc_le_comap W K)
    (Ideal.Quotient.mk _ (C r)) = Ideal.Quotient.mk _ (C (φ r))
  rw [Ideal.quotientMap_mk, MvPolynomial.map_C]

noncomputable scoped instance kw_pmbc_awayAlgCross (i : Fin 3) :
    Algebra R (Away ℬ_K ((kw_pmbc_gradedRingHom W K) (mkX_R i))) where
  smul r a := (φ r) • a
  algebraMap := (kw_pmbc_awayAlgMapK W K i).comp φ
  commutes' _ _ := mul_comm _ _
  smul_def' r a := Algebra.smul_def (φ r) a

scoped instance kw_pmbc_isScalarTower_R_K (i : Fin 3) :
    IsScalarTower R K (Away ℬ_K ((kw_pmbc_gradedRingHom W K) (mkX_R i))) :=
  ⟨fun r s a => show (r • s) • a = (φ r) • s • a by
    rw [Algebra.smul_def (R := R) r s, mul_smul]⟩

scoped instance kw_pmbc_isScalarTower_R_Away (i : Fin 3) :
    IsScalarTower R (Away ℬ_R (mkX_R i))
      (Away ℬ_K ((kw_pmbc_gradedRingHom W K) (mkX_R i))) :=
  ⟨fun r a b => by
    rw [(kw_pmbc_awayAlgR W i).smul_def r a, Algebra.smul_def, Algebra.smul_def,
      map_mul, mul_assoc]
    exact congrArg (· * (_ * b)) (kw_pmbc_awayMap_fromZero W K i r)⟩

theorem kw_pmbc_awayι_range_eq (i : Fin 2) :
    Set.range ⇑(Proj.awayι ℬ_K ((kw_pmbc_gradedRingHom W K) (mkX_R (![1, 2] i)))
        ((kw_pmbc_gradedRingHom W K).2
          (kw_no3a_wdp_mprt_pmsCR_mk_X_mem_one W.toProjective (![1, 2] i))) one_pos)
      = Set.range ⇑(pullback.fst (kw_pmbc_projModelMap W K)
          ((kw_no3a_wdp_mprt_pmsCR_openCover W.toProjective).f i)) := by
  rw [IsOpenImmersion.range_pullbackFst, ← Scheme.Hom.coe_opensRange, Proj.opensRange_awayι]
  refine congrArg SetLike.coe ?_
  refine Eq.trans ?_ (congrArg (kw_pmbc_projModelMap W K ⁻¹ᵁ ·)
    (Proj.opensRange_awayι ℬ_R (mkX_R (![1, 2] i))
      (kw_no3a_wdp_mprt_pmsCR_mk_X_mem_one W.toProjective (![1, 2] i)) one_pos).symm)
  exact Proj.map_preimage_basicOpen (kw_pmbc_gradedRingHom W K)
    (kw_pmbc_irrelevant_le W K) (mkX_R (![1, 2] i))

theorem kw_pmbc_lj_snd (i : Fin 2) :
    (IsOpenImmersion.isoOfRangeEq _ _ (kw_pmbc_awayι_range_eq W K i)).hom
        ≫ pullback.snd (kw_pmbc_projModelMap W K)
          ((kw_no3a_wdp_mprt_pmsCR_openCover W.toProjective).f i)
      = Spec.map (CommRingCat.ofHom
          (Away.map (kw_pmbc_gradedRingHom W K) (mkX_R (![1, 2] i)))) := by
  rw [← cancel_mono ((kw_no3a_wdp_mprt_pmsCR_openCover W.toProjective).f i), Category.assoc,
    ← pullback.condition, ← Category.assoc, IsOpenImmersion.isoOfRangeEq_hom_fac]
  exact Proj.awayι_comp_map (kw_pmbc_gradedRingHom W K) (kw_pmbc_irrelevant_le W K)
    one_pos (mkX_R (![1, 2] i))
    (kw_no3a_wdp_mprt_pmsCR_mk_X_mem_one W.toProjective (![1, 2] i))

theorem kw_pmbc_awayι_comp_str_K (i : Fin 2) :
    Proj.awayι ℬ_K ((kw_pmbc_gradedRingHom W K) (mkX_R (![1, 2] i)))
        ((kw_pmbc_gradedRingHom W K).2
          (kw_no3a_wdp_mprt_pmsCR_mk_X_mem_one W.toProjective (![1, 2] i))) one_pos
        ≫ projModelStrCR W_K
      = Spec.map (CommRingCat.ofHom (kw_pmbc_awayAlgMapK W K (![1, 2] i))) := by
  unfold projModelStrCR
  rw [← Category.assoc, Proj.awayι_toSpecZero, ← Spec.map_comp]
  rfl

theorem kw_pmbc_awayι_comp_str_R (i : Fin 2) :
    Proj.awayι ℬ_R (mkX_R (![1, 2] i))
        (kw_no3a_wdp_mprt_pmsCR_mk_X_mem_one W.toProjective (![1, 2] i)) one_pos
        ≫ projModelStrCR W.toProjective
      = Spec.map (CommRingCat.ofHom (kw_pmbc_awayAlgMapR W (![1, 2] i))) := by
  unfold projModelStrCR
  rw [← Category.assoc, Proj.awayι_toSpecZero, ← Spec.map_comp]
  rfl

open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

scoped instance kw_pmbc_quotTowerA {A B : Type} [CommRing A] [CommRing B] [Algebra A B]
    [Algebra R A] [Algebra R B] [IsScalarTower R A B] (I : Ideal A) :
    IsScalarTower R (A ⧸ I) (B ⧸ I.map (algebraMap A B)) :=
  IsScalarTower.of_algebraMap_eq fun r => by
    show algebraMap B _ (algebraMap R B r) = _
    rw [IsScalarTower.algebraMap_apply R A B, ← IsScalarTower.algebraMap_apply A B,
      IsScalarTower.algebraMap_apply A (A ⧸ I), ← IsScalarTower.algebraMap_apply R A (A ⧸ I)]

scoped instance kw_pmbc_quotTowerK {A B : Type} [CommRing A] [CommRing B] [Algebra A B]
    [Algebra R B] [Algebra K B] [IsScalarTower R K B] (I : Ideal A) :
    IsScalarTower R K (B ⧸ I.map (algebraMap A B)) :=
  IsScalarTower.of_algebraMap_eq fun r => by
    show algebraMap B _ (algebraMap R B r) = _
    rw [IsScalarTower.algebraMap_apply R K B, ← IsScalarTower.algebraMap_apply K B]

end IsPullback

section AwayIsPushoutHeld

variable {R : Type} [CommRing R] (W : WeierstrassCurve R)

end AwayIsPushoutHeld

section BaseChangeIso

variable {R : Type} [CommRing R] (W : WeierstrassCurve R)

end BaseChangeIso

section RowClosingWires

variable {R : Type} [CommRing R] (W : WeierstrassCurve R)

end RowClosingWires

end WeierstrassProjModel
p2m_reactivate "P2MW.S_WeierstrassProjModel_kw_bc_baseChangeIso.WeierstrassProjModel"

end
p2m_reactivate "P2MW.S_WeierstrassProjModel_kw_bc_baseChangeIso.WeierstrassProjModel"
end MEGA_KwProjModelCRBaseChangeDischarge_lean
p2m_reactivate "P2MW.S_WeierstrassProjModel_kw_bc_baseChangeIso.WeierstrassProjModel"

section SolRBcShim

noncomputable section

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra WeierstrassProjModel P2MW.S_WeierstrassProjModel_kw_bc_baseChangeIso.WeierstrassProjModel"
open MvPolynomial HomogeneousLocalization HomogeneousIdealQuotientGrading

attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false

variable {R : Type} [CommRing R] (W : WeierstrassCurve R)
variable (K : Type) [CommRing K] [Algebra R K]

local notation3 "φ" => algebraMap R K
local notation3 "W_K" => (W.map (algebraMap R K)).toProjective

private theorem sol_isPullback_spec_chart (i : Fin 2) :
    IsPullback
      (Spec.map (CommRingCat.ofHom
        (Away.map (kw_pmbc_gradedRingHom W K)
          (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
            (X (![1, 2] i) : MvPolynomial (Fin 3) R)))))
      (Spec.map (CommRingCat.ofHom (kw_pmbc_awayAlgMapK W K (![1, 2] i))))
      (Spec.map (CommRingCat.ofHom (kw_pmbc_awayAlgMapR W (![1, 2] i))))
      (Spec.map (CommRingCat.ofHom φ)) :=
  kw_bc_awayIsPushoutAll W K i

private theorem sol_isPullback_chart (i : Fin 2) :
    IsPullback
      ((kw_no3a_wdp_mprt_pmsCR_openCover W.toProjective).pullbackHom
        (kw_pmbc_projModelMap W K) i)
      (((kw_no3a_wdp_mprt_pmsCR_openCover W.toProjective).pullback₁
        (kw_pmbc_projModelMap W K)).f i ≫ projModelStrCR W_K)
      ((kw_no3a_wdp_mprt_pmsCR_openCover W.toProjective).f i ≫ projModelStrCR W.toProjective)
      (Spec.map (CommRingCat.ofHom φ)) := by
  refine (sol_isPullback_spec_chart W K i).of_iso
    (IsOpenImmersion.isoOfRangeEq _ _ (kw_pmbc_awayι_range_eq W K i))
    (Iso.refl _) (Iso.refl _) (Iso.refl _)
    ?_ ?_ ?_ (by simp)
  · rw [Iso.refl_hom, Category.comp_id, ← kw_pmbc_lj_snd W K i]; rfl
  · rw [Iso.refl_hom, Category.comp_id,
      show ((kw_no3a_wdp_mprt_pmsCR_openCover W.toProjective).pullback₁
          (kw_pmbc_projModelMap W K)).f i
        = pullback.fst (kw_pmbc_projModelMap W K)
          ((kw_no3a_wdp_mprt_pmsCR_openCover W.toProjective).f i) from rfl,
      ← Category.assoc, IsOpenImmersion.isoOfRangeEq_hom_fac]
    exact (kw_pmbc_awayι_comp_str_K W K i).symm
  · rw [Iso.refl_hom, Iso.refl_hom, Category.comp_id, Category.id_comp]
    exact (kw_pmbc_awayι_comp_str_R W i).symm

private theorem sol_isPullback_of_C1 :
    IsPullback (kw_pmbc_projModelMap W K) (projModelStrCR W_K)
      (projModelStrCR W.toProjective) (Spec.map (CommRingCat.ofHom φ)) :=
  Scheme.isPullback_of_openCover _ _ _ _
    (kw_no3a_wdp_mprt_pmsCR_openCover W.toProjective)
    fun i => sol_isPullback_chart W K i

end
p2m_reactivate "P2MW.S_WeierstrassProjModel_kw_bc_baseChangeIso.WeierstrassProjModel"

end SolRBcShim
p2m_reactivate "P2MW.S_WeierstrassProjModel_kw_bc_baseChangeIso.WeierstrassProjModel"

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra _root_.WeierstrassProjModel _root_.P2MW.S_WeierstrassProjModel_kw_bc_baseChangeIso.WeierstrassProjModel in
theorem solution {R : Type} [CommRing R]
    (W : WeierstrassCurve R) :
    ∀ (K : Type) [Field K] [Algebra R K],
      Nonempty (pullback (projModelStrCR W.toProjective)
          (Spec.map (CommRingCat.ofHom (algebraMap R K)))
        ≅ projModelCR (W.toProjective.baseChange K)) := by
  intro K _ _
  exact ⟨(sol_isPullback_of_C1 W K).isoPullback.symm⟩

end S_WeierstrassProjModel_kw_bc_baseChangeIso
end P2MW
export P2MW.S_WeierstrassProjModel_kw_bc_baseChangeIso (solution)
