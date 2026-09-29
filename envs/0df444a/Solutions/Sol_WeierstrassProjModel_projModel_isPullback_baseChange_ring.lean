-- Prove2me | solution 1 for WeierstrassProjModel.projModel_isPullback_baseChange_ring
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/be68b5ae-97cc-56f0-abd8-f2425a2b4bd0

import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Theorems.Thm_WeierstrassProjModel_kw_bc_awayIsPushout_Y_univ
import Theorems.Thm_WeierstrassProjModel_kw_bc_awayIsPushout_Z_univ
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassProjModel_projModel_isPullback_baseChange_ring

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits WeierstrassCurve
open MvPolynomial HomogeneousLocalization HomogeneousIdealQuotientGrading

namespace WeierstrassProjModel
p2m_export "WeierstrassProjModel" "projModelHomogeneousIdealCR projModelHomogeneousIdealCR_toIdeal projModelGradingCR projModelCR projModelStrCR kw_pbac_mk_X_mem_one_CR kw_pbac_irrelevant_le_span_mk_X_CR kw_bc_awayIsPushout_Y_univ kw_bc_awayIsPushout_Z_univ"
p2m_open "WeierstrassProjModel"

namespace ProjBaseChange

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

section GradedHom

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)
variable (K : Type u) [CommRing K] [Algebra R K]

local notation3 "φ" => algebraMap R K
local notation3 "W_K" => (W.map (algebraMap R K)).toProjective

theorem map_span_polynomial :
    (Ideal.span {W.toProjective.polynomial}).map (MvPolynomial.map φ)
      = Ideal.span {(W_K).polynomial} := by
  rw [Ideal.map_span, Set.image_singleton, WeierstrassCurve.Projective.map_polynomial]

theorem le_comap :
    (projModelHomogeneousIdealCR W.toProjective).toIdeal
      ≤ Ideal.comap (MvPolynomial.map φ) (projModelHomogeneousIdealCR W_K).toIdeal := by
  rw [projModelHomogeneousIdealCR_toIdeal, projModelHomogeneousIdealCR_toIdeal,
    ← map_span_polynomial W K]
  exact Ideal.le_comap_map

def gradedRingHom :
    (projModelGradingCR W.toProjective) →+*ᵍ (projModelGradingCR W_K) :=
  { toRingHom := Ideal.quotientMap _ (MvPolynomial.map (algebraMap R K)) <| by
      rw [projModelHomogeneousIdealCR_toIdeal, projModelHomogeneousIdealCR_toIdeal]
      have h : (Ideal.span {W.toProjective.polynomial}).map
            (MvPolynomial.map (algebraMap R K))
          = Ideal.span {(W.map (algebraMap R K)).toProjective.polynomial} := by
        rw [Ideal.map_span, Set.image_singleton,
          WeierstrassCurve.Projective.map_polynomial]
      rw [← h]
      exact Ideal.le_comap_map,
    map_mem := by
      rintro n _ ⟨p, hp, rfl⟩
      exact mk_mem_quotGradingSubmodule _ _
        ((mem_homogeneousSubmodule _ _).mpr
          (((mem_homogeneousSubmodule _ _).mp hp).map (algebraMap R K))) }

theorem gradedRingHom_mk_X (i : Fin 3) :
    gradedRingHom W K (Ideal.Quotient.mk _ (X i : MvPolynomial (Fin 3) R))
      = Ideal.Quotient.mk _ (X i : MvPolynomial (Fin 3) K) := by
  show Ideal.quotientMap _ (MvPolynomial.map φ) (le_comap W K)
    (Ideal.Quotient.mk _ (X i : MvPolynomial (Fin 3) R)) = _
  rw [Ideal.quotientMap_mk, MvPolynomial.map_X]

theorem irrelevant_le :
    HomogeneousIdeal.irrelevant (projModelGradingCR W_K)
      ≤ (HomogeneousIdeal.irrelevant (projModelGradingCR W.toProjective)).map
          (gradedRingHom W K) := by
  intro x hx
  have hspan : x ∈ (Ideal.span (Set.range fun i : Fin 3 =>
      Ideal.Quotient.mk _ (X i : MvPolynomial (Fin 3) K))) :=
    kw_pbac_irrelevant_le_span_mk_X_CR K W_K hx
  refine (Ideal.span_le.mpr ?_) hspan
  rintro _ ⟨i, rfl⟩
  show Ideal.Quotient.mk _ (X i : MvPolynomial (Fin 3) K)
    ∈ (HomogeneousIdeal.map (gradedRingHom W K)
        (HomogeneousIdeal.irrelevant (projModelGradingCR W.toProjective)))
  rw [← gradedRingHom_mk_X W K i, ← HomogeneousIdeal.mem_iff, HomogeneousIdeal.toIdeal_map]
  exact Ideal.mem_map_of_mem _ (HomogeneousIdeal.mem_irrelevant_of_mem _ one_pos
    (kw_pbac_mk_X_mem_one_CR R W.toProjective i))

def projModelMap : projModelCR W_K ⟶ projModelCR W.toProjective :=
  Proj.map (gradedRingHom W K) (irrelevant_le W K)

end GradedHom

section TwoChartCover

variable {R : Type u} [CommRing R]

def zCofactor (V : WeierstrassCurve.Projective R) : MvPolynomial (Fin 3) R :=
  X 1 ^ 2 + C V.a₁ * X 0 * X 1 + C V.a₃ * X 1 * X 2
    - C V.a₂ * X 0 ^ 2 - C V.a₄ * X 0 * X 2 - C V.a₆ * X 2 ^ 2

theorem polynomial_add_X0_cube (V : WeierstrassCurve.Projective R) :
    V.polynomial + X 0 ^ 3 = X 2 * zCofactor V := by
  rw [WeierstrassCurve.Projective.polynomial, zCofactor]
  ring

theorem mk_X0_cube_mem_span_mk_X2 (V : WeierstrassCurve.Projective R) :
    (Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal
        (X 0 : MvPolynomial (Fin 3) R)) ^ 3
      ∈ Ideal.span {Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal
          (X 2 : MvPolynomial (Fin 3) R)} := by
  have hpoly : Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal V.polynomial = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  have hid := congrArg (Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal)
    (polynomial_add_X0_cube V)
  rw [map_add, map_mul, map_pow, hpoly, zero_add] at hid
  rw [hid, Ideal.mem_span_singleton]
  exact ⟨_, rfl⟩

theorem not_both_in_ideal (V : WeierstrassCurve.Projective R)
    (x : Proj (projModelGradingCR V))
    (h1 : Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal
        (X 1 : MvPolynomial (Fin 3) R) ∈ x.asHomogeneousIdeal.toIdeal)
    (h2 : Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal
        (X 2 : MvPolynomial (Fin 3) R) ∈ x.asHomogeneousIdeal.toIdeal) :
    False := by
  have h0cube : (Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal
        (X 0 : MvPolynomial (Fin 3) R)) ^ 3 ∈ x.asHomogeneousIdeal.toIdeal :=
    (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr h2)) (mk_X0_cube_mem_span_mk_X2 V)
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
    hspan (kw_pbac_irrelevant_le_span_mk_X_CR R V hz)

theorem awayι_jointly_surjective
    (V : WeierstrassCurve.Projective R) (x : Proj (projModelGradingCR V)) :
    ∃ (i : Fin 2)
      (u : Spec (CommRingCat.of (HomogeneousLocalization.Away (projModelGradingCR V)
        (Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal
          (X (![1, 2] i) : MvPolynomial (Fin 3) R))))),
      (Proj.awayι (projModelGradingCR V) _
          (kw_pbac_mk_X_mem_one_CR R V (![1, 2] i)) Nat.one_pos) u = x := by
  by_cases hZ : Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal
      (X 2 : MvPolynomial (Fin 3) R) ∈ x.asHomogeneousIdeal.toIdeal
  · by_cases hY : Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal
        (X 1 : MvPolynomial (Fin 3) R) ∈ x.asHomogeneousIdeal.toIdeal
    · exact (not_both_in_ideal V x hY hZ).elim
    · have hrange : x ∈ (Proj.awayι (projModelGradingCR V) _
          (kw_pbac_mk_X_mem_one_CR R V 1) Nat.one_pos).opensRange := by
        rw [Proj.opensRange_awayι]
        exact hY
      obtain ⟨u, hu⟩ := Scheme.Hom.mem_opensRange.mp hrange
      exact ⟨0, u, hu⟩
  · have hrange : x ∈ (Proj.awayι (projModelGradingCR V) _
        (kw_pbac_mk_X_mem_one_CR R V 2) Nat.one_pos).opensRange := by
      rw [Proj.opensRange_awayι]
      exact hZ
    obtain ⟨u, hu⟩ := Scheme.Hom.mem_opensRange.mp hrange
    exact ⟨1, u, hu⟩

noncomputable def twoChartOpenCover (V : WeierstrassCurve.Projective R) :
    (Proj (projModelGradingCR V)).OpenCover :=
  Scheme.Cover.mkOfCovers (Fin 2)
    (fun i => Spec (CommRingCat.of (HomogeneousLocalization.Away (projModelGradingCR V)
      (Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal
        (X (![1, 2] i) : MvPolynomial (Fin 3) R)))))
    (fun i => Proj.awayι (projModelGradingCR V) _
      (kw_pbac_mk_X_mem_one_CR R V (![1, 2] i)) Nat.one_pos)
    (awayι_jointly_surjective V)

end TwoChartCover

section IsPullback

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)
variable (K : Type u) [CommRing K] [Algebra R K]

local notation3 "φ" => algebraMap R K
local notation3 "W_K" => (W.map (algebraMap R K)).toProjective
local notation3 "ℬ_R" => projModelGradingCR W.toProjective
local notation3 "ℬ_K" => projModelGradingCR W_K
local notation3 "mkX_R" i =>
  Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
    (X i : MvPolynomial (Fin 3) R)

def awayAlgMapR (i : Fin 3) : R →+* Away ℬ_R (mkX_R i) :=
  (fromZeroRingHom ℬ_R (Submonoid.powers (mkX_R i))).comp (algebraMap R ↥(ℬ_R 0))

def awayAlgMapK (i : Fin 3) : K →+* Away ℬ_K ((gradedRingHom W K) (mkX_R i)) :=
  (fromZeroRingHom ℬ_K (Submonoid.powers ((gradedRingHom W K) (mkX_R i)))).comp
    (algebraMap K ↥(ℬ_K 0))

def ChartSquares : Prop :=
  ∀ i : Fin 2,
    IsPullback
      (Spec.map (CommRingCat.ofHom (Away.map (gradedRingHom W K) (mkX_R (![1, 2] i)))))
      (Spec.map (CommRingCat.ofHom (awayAlgMapK W K (![1, 2] i))))
      (Spec.map (CommRingCat.ofHom (awayAlgMapR W (![1, 2] i))))
      (Spec.map (CommRingCat.ofHom φ))

theorem awayι_range_eq (i : Fin 2) :
    Set.range ⇑(Proj.awayι ℬ_K ((gradedRingHom W K) (mkX_R (![1, 2] i)))
        ((gradedRingHom W K).2
          (kw_pbac_mk_X_mem_one_CR R W.toProjective (![1, 2] i))) one_pos)
      = Set.range ⇑(pullback.fst (projModelMap W K)
          ((twoChartOpenCover W.toProjective).f i)) := by
  rw [IsOpenImmersion.range_pullbackFst, ← Scheme.Hom.coe_opensRange, Proj.opensRange_awayι]
  refine congrArg SetLike.coe ?_
  refine Eq.trans ?_ (congrArg (projModelMap W K ⁻¹ᵁ ·)
    (Proj.opensRange_awayι ℬ_R (mkX_R (![1, 2] i))
      (kw_pbac_mk_X_mem_one_CR R W.toProjective (![1, 2] i)) one_pos).symm)
  exact Proj.map_preimage_basicOpen (gradedRingHom W K) (irrelevant_le W K) (mkX_R (![1, 2] i))

theorem isoOfRangeEq_snd (i : Fin 2) :
    (IsOpenImmersion.isoOfRangeEq _ _ (awayι_range_eq W K i)).hom
        ≫ pullback.snd (projModelMap W K) ((twoChartOpenCover W.toProjective).f i)
      = Spec.map (CommRingCat.ofHom
          (Away.map (gradedRingHom W K) (mkX_R (![1, 2] i)))) := by
  rw [← cancel_mono ((twoChartOpenCover W.toProjective).f i), Category.assoc,
    ← pullback.condition, ← Category.assoc, IsOpenImmersion.isoOfRangeEq_hom_fac]
  exact Proj.awayι_comp_map (gradedRingHom W K) (irrelevant_le W K)
    one_pos (mkX_R (![1, 2] i))
    (kw_pbac_mk_X_mem_one_CR R W.toProjective (![1, 2] i))

theorem awayι_comp_str_K (i : Fin 2) :
    Proj.awayι ℬ_K ((gradedRingHom W K) (mkX_R (![1, 2] i)))
        ((gradedRingHom W K).2
          (kw_pbac_mk_X_mem_one_CR R W.toProjective (![1, 2] i))) one_pos
        ≫ projModelStrCR W_K
      = Spec.map (CommRingCat.ofHom (awayAlgMapK W K (![1, 2] i))) := by
  unfold projModelStrCR
  rw [← Category.assoc, Proj.awayι_toSpecZero, ← Spec.map_comp]
  rfl

theorem awayι_comp_str_R (i : Fin 2) :
    Proj.awayι ℬ_R (mkX_R (![1, 2] i))
        (kw_pbac_mk_X_mem_one_CR R W.toProjective (![1, 2] i)) one_pos
        ≫ projModelStrCR W.toProjective
      = Spec.map (CommRingCat.ofHom (awayAlgMapR W (![1, 2] i))) := by
  unfold projModelStrCR
  rw [← Category.assoc, Proj.awayι_toSpecZero, ← Spec.map_comp]
  rfl

theorem isPullback_chart (h : ChartSquares W K) (i : Fin 2) :
    IsPullback
      ((twoChartOpenCover W.toProjective).pullbackHom (projModelMap W K) i)
      (((twoChartOpenCover W.toProjective).pullback₁ (projModelMap W K)).f i
        ≫ projModelStrCR W_K)
      ((twoChartOpenCover W.toProjective).f i ≫ projModelStrCR W.toProjective)
      (Spec.map (CommRingCat.ofHom φ)) := by
  refine (h i).of_iso
    (IsOpenImmersion.isoOfRangeEq _ _ (awayι_range_eq W K i))
    (Iso.refl _) (Iso.refl _) (Iso.refl _)
    ?_ ?_ ?_ (by simp)
  · rw [Iso.refl_hom, Category.comp_id, ← isoOfRangeEq_snd W K i]; rfl
  · rw [Iso.refl_hom, Category.comp_id,
      show ((twoChartOpenCover W.toProjective).pullback₁ (projModelMap W K)).f i
        = pullback.fst (projModelMap W K) ((twoChartOpenCover W.toProjective).f i) from rfl,
      ← Category.assoc, IsOpenImmersion.isoOfRangeEq_hom_fac]
    exact (awayι_comp_str_K W K i).symm
  · rw [Iso.refl_hom, Iso.refl_hom, Category.comp_id, Category.id_comp]
    exact (awayι_comp_str_R W i).symm

theorem isPullback (h : ChartSquares W K) :
    IsPullback (projModelMap W K) (projModelStrCR W_K)
      (projModelStrCR W.toProjective) (Spec.map (CommRingCat.ofHom φ)) :=
  Scheme.isPullback_of_openCover _ _ _ _ (twoChartOpenCover W.toProjective)
    fun i => isPullback_chart W K h i

def pullbackIso (h : ChartSquares W K) :
    pullback (projModelStrCR W.toProjective) (Spec.map (CommRingCat.ofHom φ))
      ≅ projModelCR W_K :=
  (isPullback W K h).isoPullback.symm

end IsPullback

end ProjBaseChange

end WeierstrassProjModel

end

p2m_open "AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel P2MW.S_WeierstrassProjModel_projModel_isPullback_baseChange_ring.WeierstrassProjModel"

universe u

theorem solution {R : Type u} [CommRing R] (V : WeierstrassCurve.Projective R)
    (K : Type u) [CommRing K] [Algebra R K] :
    ∃ (α : projModelCR (V.baseChange K) ⟶ projModelCR V),
      IsPullback α (projModelStrCR (V.baseChange K)) (projModelStrCR V)
        (Spec.map (CommRingCat.ofHom (algebraMap R K))) :=
  ⟨WeierstrassProjModel.ProjBaseChange.projModelMap V K,
    WeierstrassProjModel.ProjBaseChange.isPullback V K (fun i => by
      fin_cases i <;> simp only [Fin.isValue]
      · exact WeierstrassProjModel.kw_bc_awayIsPushout_Y_univ V K
      · exact WeierstrassProjModel.kw_bc_awayIsPushout_Z_univ V K)⟩

end S_WeierstrassProjModel_projModel_isPullback_baseChange_ring
end P2MW
export P2MW.S_WeierstrassProjModel_projModel_isPullback_baseChange_ring (solution)
