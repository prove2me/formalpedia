-- Prove2me | solution 1 for V3Asm.exc_rational
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/1ad9640a-313b-5072-a7d2-055d2a85ce32

import Mathlib
import Definitions.Def_ModularCurve_ResolvedModelSite
import Theorems.Thm_MvPolynomial_CrossingQuotient_Resolution_exists_twoAffineLineCover_subscheme_of_chartTable
import Theorems.Thm_AlgebraicCurve_CurveModel_exists_iso_of_twoAffineLineCover
import Theorems.Thm_MvPolynomial_CrossingQuotient_Resolution_comap_iota_vanishingIdeal_closure_lines
import Theorems.Thm_AlgebraicGeometry_isIso_fiberToSpecResidueField_of_preimage_eq_singleton_of_isIso_residueFieldMap
import Theorems.Thm_AlgebraicGeometry_IsClosedImmersion_exists_iso_hom_comp_eq_of_range_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_V3Asm_exc_rational
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation"
p2m_attr_erase "simp" "AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces"

set_option autoImplicit false
set_option maxHeartbeats 1600000

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_V3Asm_exc_rational.AlgebraicGeometry TopologicalSpace Polynomial AlgebraicGeometry.Polynomial"

universe u

namespace TwoAffineLineCover

attribute [local instance] Polynomial.algebra

variable {k κ : Type u} [CommRing k] [CommRing κ] [Algebra k κ]

noncomputable abbrev locMap : Localization.Away (X : k[X]) →+* Localization.Away (X : κ[X]) :=
  IsLocalization.map (M := Submonoid.powers (X : k[X])) (T := Submonoid.powers (X : κ[X])) _
    (mapRingHom (algebraMap k κ)) (by
      rintro _ ⟨n, rfl⟩
      exact ⟨n, by simp⟩)

theorem locMap_comp_algebraMap :
    (locMap (k := k) (κ := κ)).comp (algebraMap k[X] (Localization.Away (X : k[X]))) =
      (algebraMap κ[X] (Localization.Away (X : κ[X]))).comp (mapRingHom (algebraMap k κ)) :=
  IsLocalization.map_comp _

theorem aeval_invSelf_comp_mapRingHom :
    (aeval (R := κ) (IsLocalization.Away.invSelf (S := Localization.Away (X : κ[X])) (X : κ[X]))).toRingHom.comp
        (mapRingHom (algebraMap k κ)) =
      (locMap (k := k) (κ := κ)).comp
        (aeval (R := k) (IsLocalization.Away.invSelf (S := Localization.Away (X : k[X])) (X : k[X]))).toRingHom := by
  refine Polynomial.ringHom_ext (fun a => ?_) ?_
  · simp only [RingHom.coe_comp, Function.comp_apply, coe_mapRingHom, map_C, AlgHom.toRingHom_eq_coe,
      AlgHom.coe_toRingHom, aeval_C]
    rw [IsScalarTower.algebraMap_apply k k[X] (Localization.Away (X : k[X])) a, IsLocalization.map_eq,
      Polynomial.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, coe_mapRingHom, Polynomial.map_C,
      IsScalarTower.algebraMap_apply κ κ[X] (Localization.Away (X : κ[X])) (algebraMap k κ a),
      Polynomial.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
  · simp only [RingHom.coe_comp, Function.comp_apply, coe_mapRingHom, map_X, AlgHom.toRingHom_eq_coe,
      AlgHom.coe_toRingHom, aeval_X]
    rw [IsLocalization.Away.invSelf, IsLocalization.Away.invSelf, IsLocalization.map_mk']
    simp

variable (k κ) in

theorem isPullback_polynomial :
    IsPullback (Spec.map (CommRingCat.ofHom (algebraMap κ κ[X])))
      (Spec.map (CommRingCat.ofHom (algebraMap k[X] κ[X])))
      (Spec.map (CommRingCat.ofHom (algebraMap k κ))) (Spec.map (CommRingCat.ofHom (algebraMap k k[X]))) :=
  isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_of_isPushout k κ k[X] κ[X])

variable (k κ) in

theorem isPullback_away :
    IsPullback (Spec.map (CommRingCat.ofHom (algebraMap κ[X] (Localization.Away (X : κ[X])))))
      (Spec.map (CommRingCat.ofHom (locMap (k := k) (κ := κ))))
      (Spec.map (CommRingCat.ofHom (algebraMap k[X] κ[X])))
      (Spec.map (CommRingCat.ofHom (algebraMap k[X] (Localization.Away (X : k[X]))))) := by
  letI : Algebra (Localization.Away (X : k[X])) (Localization.Away (X : κ[X])) := (locMap (k := k) (κ := κ)).toAlgebra
  haveI : IsScalarTower k[X] (Localization.Away (X : k[X])) (Localization.Away (X : κ[X])) :=
    IsScalarTower.of_algebraMap_eq' (R := k[X]) (S := Localization.Away (X : k[X])) (A := Localization.Away (X : κ[X])) (by
      rw [RingHom.algebraMap_toAlgebra, IsScalarTower.algebraMap_eq k[X] κ[X] (Localization.Away (X : κ[X])),
        Polynomial.algebraMap_def, locMap_comp_algebraMap])

  have hM : Algebra.algebraMapSubmonoid κ[X] (Submonoid.powers (X : k[X])) = Submonoid.powers (X : κ[X]) := by
    ext p
    simp only [Algebra.algebraMapSubmonoid, Submonoid.mem_map, Submonoid.mem_powers_iff]
    constructor
    · rintro ⟨_, ⟨n, rfl⟩, rfl⟩; exact ⟨n, by simp [Polynomial.algebraMap_def]⟩
    · rintro ⟨n, rfl⟩; exact ⟨X ^ n, ⟨n, rfl⟩, by simp [Polynomial.algebraMap_def]⟩
  haveI : IsLocalization (Algebra.algebraMapSubmonoid κ[X] (Submonoid.powers (X : k[X]))) (Localization.Away (X : κ[X])) := by
    rw [hM]; infer_instance
  haveI : Algebra.IsPushout k[X] κ[X] (Localization.Away (X : k[X])) (Localization.Away (X : κ[X])) :=
    (Algebra.isLocalization_iff_isPushout (Submonoid.powers (X : k[X])) (Localization.Away (X : k[X]))).mp inferInstance
  exact isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_of_isPushout k[X] κ[X] (Localization.Away (X : k[X])) (Localization.Away (X : κ[X])))

section

variable {Z : Scheme.{u}} (z : Z ⟶ Spec (CommRingCat.of k))
  (i : Spec (CommRingCat.of k[X]) ⟶ Z) (hi : i ≫ z = Spec.map (CommRingCat.ofHom (algebraMap k k[X])))

noncomputable def bcChart : Spec (CommRingCat.of κ[X]) ⟶ pullback z (Spec.map (CommRingCat.ofHom (algebraMap k κ))) :=
  pullback.lift (Spec.map (CommRingCat.ofHom (algebraMap k[X] κ[X])) ≫ i)
    (Spec.map (CommRingCat.ofHom (algebraMap κ κ[X])))
    (by rw [Category.assoc, hi, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
          ← IsScalarTower.algebraMap_eq, ← IsScalarTower.algebraMap_eq])

@[reassoc (attr := simp)]
theorem bcChart_fst : bcChart z i hi ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (algebraMap k[X] κ[X])) ≫ i :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem bcChart_snd : bcChart z i hi ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom (algebraMap κ κ[X])) :=
  pullback.lift_snd _ _ _

theorem isPullback_bcChart :
    IsPullback (bcChart (κ := κ) z i hi) (Spec.map (CommRingCat.ofHom (algebraMap k[X] κ[X]))) (pullback.fst _ _) i := by
  refine IsPullback.of_right (h₁₂ := pullback.snd z (Spec.map (CommRingCat.ofHom (algebraMap k κ))))
    (v₁₃ := Spec.map (CommRingCat.ofHom (algebraMap k κ))) (h₂₂ := z) ?_ (bcChart_fst z i hi) ?_
  · rw [bcChart_snd, hi]
    exact isPullback_polynomial k κ
  · exact (IsPullback.of_hasPullback z (Spec.map (CommRingCat.ofHom (algebraMap k κ)))).flip

scoped instance [IsOpenImmersion i] : IsOpenImmersion (bcChart (κ := κ) z i hi) :=
  MorphismProperty.of_isPullback (isPullback_bcChart z i hi).flip ‹_›

theorem range_bcChart :
    Set.range (bcChart (κ := κ) z i hi).base = (pullback.fst z (Spec.map (CommRingCat.ofHom (algebraMap k κ)))).base ⁻¹' Set.range i.base := by
  have h := isPullback_bcChart (κ := κ) z i hi
  rw [← Scheme.Pullback.range_fst (pullback.fst z (Spec.map (CommRingCat.ofHom (algebraMap k κ)))) i,
    ← h.isoPullback_hom_fst, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    Set.range_eq_univ.mpr (fun y => ⟨h.isoPullback.inv y, by rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id]; rfl⟩),
    Set.image_univ]

theorem range_away_bcChart :
    Set.range (Spec.map (CommRingCat.ofHom (algebraMap κ[X] (Localization.Away (X : κ[X])))) ≫ bcChart (κ := κ) z i hi).base =
      (pullback.fst z (Spec.map (CommRingCat.ofHom (algebraMap k κ)))).base ⁻¹'
        Set.range (Spec.map (CommRingCat.ofHom (algebraMap k[X] (Localization.Away (X : k[X])))) ≫ i).base := by
  have h := (isPullback_away k κ).paste_horiz (isPullback_bcChart (κ := κ) z i hi)
  rw [← Scheme.Pullback.range_fst (pullback.fst z (Spec.map (CommRingCat.ofHom (algebraMap k κ)))) _,
    ← h.isoPullback_hom_fst, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    Set.range_eq_univ.mpr (fun y => ⟨h.isoPullback.inv y, by rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id]; rfl⟩),
    Set.image_univ]

end

theorem baseChange {Z : Scheme.{u}} (z : Z ⟶ Spec (CommRingCat.of k))
    (i₀ i₁ : Spec (CommRingCat.of k[X]) ⟶ Z) [IsOpenImmersion i₀] [IsOpenImmersion i₁]
    (hi₀ : i₀ ≫ z = Spec.map (CommRingCat.ofHom (algebraMap k k[X])))
    (hi₁ : i₁ ≫ z = Spec.map (CommRingCat.ofHom (algebraMap k k[X])))
    (hcov : Set.range i₀.base ∪ Set.range i₁.base = Set.univ)
    (hglue : Spec.map (CommRingCat.ofHom (algebraMap k[X] (Localization.Away (X : k[X])))) ≫ i₀ =
      Spec.map (CommRingCat.ofHom (aeval (R := k)
        (IsLocalization.Away.invSelf (S := Localization.Away (X : k[X])) (X : k[X]))).toRingHom) ≫ i₁)
    (hmeet : Set.range i₀.base ∩ Set.range i₁.base ⊆
      Set.range (Spec.map (CommRingCat.ofHom (algebraMap k[X] (Localization.Away (X : k[X])))) ≫ i₀).base) :
    ∃ (i₀' i₁' : Spec (CommRingCat.of κ[X]) ⟶ pullback z (Spec.map (CommRingCat.ofHom (algebraMap k κ))))
      (_ : IsOpenImmersion i₀') (_ : IsOpenImmersion i₁'),
      i₀' ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom (algebraMap κ κ[X])) ∧
      i₁' ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom (algebraMap κ κ[X])) ∧
      Set.range i₀'.base ∪ Set.range i₁'.base = Set.univ ∧
      Spec.map (CommRingCat.ofHom (algebraMap κ[X] (Localization.Away (X : κ[X])))) ≫ i₀' =
        Spec.map (CommRingCat.ofHom (aeval (R := κ)
          (IsLocalization.Away.invSelf (S := Localization.Away (X : κ[X])) (X : κ[X]))).toRingHom) ≫ i₁' ∧
      Set.range i₀'.base ∩ Set.range i₁'.base ⊆
        Set.range (Spec.map (CommRingCat.ofHom (algebraMap κ[X] (Localization.Away (X : κ[X])))) ≫ i₀').base ∧
      i₀' ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (algebraMap k[X] κ[X])) ≫ i₀ ∧
      i₁' ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (algebraMap k[X] κ[X])) ≫ i₁ := by
  refine ⟨bcChart z i₀ hi₀, bcChart z i₁ hi₁, inferInstance, inferInstance, bcChart_snd z i₀ hi₀, bcChart_snd z i₁ hi₁,
    ?_, ?_, ?_, bcChart_fst z i₀ hi₀, bcChart_fst z i₁ hi₁⟩
  ·
    rw [range_bcChart, range_bcChart, ← Set.preimage_union, hcov, Set.preimage_univ]
  ·
    have hL : Spec.map (CommRingCat.ofHom (algebraMap κ[X] (Localization.Away (X : κ[X])))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k[X] κ[X])) =
        Spec.map (CommRingCat.ofHom (locMap (k := k) (κ := κ))) ≫
          Spec.map (CommRingCat.ofHom (algebraMap k[X] (Localization.Away (X : k[X])))) := by
      rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
        Polynomial.algebraMap_def, locMap_comp_algebraMap]
    have hR : Spec.map (CommRingCat.ofHom (aeval (R := κ)
          (IsLocalization.Away.invSelf (S := Localization.Away (X : κ[X])) (X : κ[X]))).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k[X] κ[X])) =
        Spec.map (CommRingCat.ofHom (locMap (k := k) (κ := κ))) ≫
          Spec.map (CommRingCat.ofHom (aeval (R := k)
            (IsLocalization.Away.invSelf (S := Localization.Away (X : k[X])) (X : k[X]))).toRingHom) := by
      rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
        Polynomial.algebraMap_def, aeval_invSelf_comp_mapRingHom]
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, bcChart_fst, bcChart_fst, ← Category.assoc, hL, Category.assoc, hglue,
        ← Category.assoc, ← hR, Category.assoc]
    · rw [Category.assoc, Category.assoc, bcChart_snd, bcChart_snd, ← Spec.map_comp, ← Spec.map_comp,
        ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq, AlgHom.toRingHom_eq_coe,
        AlgHom.comp_algebraMap]
  ·
    rw [range_bcChart, range_bcChart, ← Set.preimage_inter, range_away_bcChart]
    exact Set.preimage_mono hmeet

end TwoAffineLineCover
p2m_reactivate "P2MW.S_V3Asm_exc_rational.TwoAffineLineCover"

namespace MvPolynomial
p2m_export "MvPolynomial" "X map R zeroLocus aeval_X ext algebraMap_def support algebraMap_apply ringHom_ext comap vanishingIdeal algebraMap_eq map_C C map_X aeval_C aeval CrossingQuotient.Resolution CrossingQuotient.U CrossingQuotient.V CrossingQuotient.U_mul_V CrossingQuotient CrossingQuotient.isMaximal_vertexIdeal CrossingQuotient.Resolution.comap_iota_vanishingIdeal_closure_lines"
namespace CrossingQuotient
p2m_export "MvPolynomial.CrossingQuotient" "Resolution Resolution.ι Resolution.toSpec U V U_mul_V lift mk_surjective lineVIdeal lineUIdeal V_mem_lineVIdeal isMaximal_vertexIdeal lineUIdeal_le_iff lineVIdeal_le_iff Resolution.lineGen Resolution.lineUGen Resolution.lineUGen_eq_lineGen_succ Resolution.mem_closure_lineGen_iff Resolution.comap_iota_vanishingIdeal_closure_lines"
namespace Resolution
p2m_export "MvPolynomial.CrossingQuotient.Resolution" "ι openCover toSpec hom_ext lineGen lineUGen lineUGen_eq_lineGen_succ mem_closure_lineGen_iff exists_twoAffineLineCover_subscheme_of_chartTable comap_iota_vanishingIdeal_closure_lines"
p2m_open "MvPolynomial.CrossingQuotient.Resolution MvPolynomial.CrossingQuotient MvPolynomial"

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_V3Asm_exc_rational.AlgebraicGeometry Polynomial AlgebraicGeometry.Polynomial P2MW.S_V3Asm_exc_rational.TwoAffineLineCover"

variable {W : Type u} [CommRing W] (t : W) (e : ℕ)

theorem isPullback_of_comp_mono {C : Type*} [Category C] {X Y S S' : C} (a : X ⟶ S) (b : Y ⟶ S) (m : S ⟶ S') [Mono m]
    [HasPullback a b] :
    IsPullback (pullback.fst a b) (pullback.snd a b) (a ≫ m) (b ≫ m) :=
  IsPullback.of_isLimit (pullbackIsPullbackOfCompMono a b m)

theorem exists_twoAffineLineCover_pullback_subschemeι
    (F : Fin (e + 1) → (Resolution t e).IdealSheafData)
    (hF : ∀ (i : Fin e) (k : Fin (e + 1)), (F k).comap (Resolution.ι t e i) =
      Scheme.IdealSheafData.ofIdealTop (Ideal.map (Scheme.ΓSpecIso (CommRingCat.of (CrossingQuotient W t))).inv.hom
        (if (k : ℕ) = (i : ℕ) then Ideal.span {V t} else if (k : ℕ) = (i : ℕ) + 1 then Ideal.span {U t} else ⊤)))
    (d : ℕ) (hd0 : 0 < d) (hde : d < e)
    (k₀ : Type u) [Field k₀] [Algebra W k₀] (hq : Function.Surjective (algebraMap W k₀))
    (hker : RingHom.ker (algebraMap W k₀) = Ideal.span {t})
    (κ : Type u) [CommRing κ] (toκ : W →+* κ) (htoκ : toκ t = 0) :
    ∃ (i₀ i₁ : Spec (CommRingCat.of κ[X]) ⟶
        pullback ((F ⟨d, by omega⟩).subschemeι ≫ Resolution.toSpec t e) (Spec.map (CommRingCat.ofHom toκ))),
      IsOpenImmersion i₀ ∧ IsOpenImmersion i₁ ∧
      i₀ ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom (algebraMap κ κ[X])) ∧
      i₁ ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom (algebraMap κ κ[X])) ∧
      Set.range i₀.base ∪ Set.range i₁.base = Set.univ ∧
      Spec.map (CommRingCat.ofHom (algebraMap κ[X] (Localization.Away (Polynomial.X : κ[X])))) ≫ i₀ =
        Spec.map (CommRingCat.ofHom (Polynomial.aeval (R := κ)
          (IsLocalization.Away.invSelf (S := Localization.Away (Polynomial.X : κ[X])) (Polynomial.X : κ[X]))).toRingHom) ≫ i₁ ∧
      Set.range i₀.base ∩ Set.range i₁.base ⊆
        Set.range (Spec.map (CommRingCat.ofHom (algebraMap κ[X] (Localization.Away (Polynomial.X : κ[X])))) ≫ i₀).base := by

  obtain ⟨z, j₀, j₁, hJ₀, hJ₁, hz, hj₀, hj₁, hcov, hglue, hmeet, -, -⟩ :=
    exists_twoAffineLineCover_subscheme_of_chartTable t e F hF d hd0 hde k₀ hq hker

  have hle : RingHom.ker (algebraMap W k₀) ≤ RingHom.ker toκ := by
    rw [hker, Ideal.span_singleton_le_iff_mem, RingHom.mem_ker]
    exact htoκ
  let g : k₀ →+* κ := RingHom.liftOfSurjective (algebraMap W k₀) hq ⟨toκ, hle⟩
  have hg : g.comp (algebraMap W k₀) = toκ := RingHom.liftOfSurjective_comp _ hq ⟨toκ, hle⟩
  letI : Algebra k₀ κ := g.toAlgebra
  have hgalg : algebraMap k₀ κ = g := rfl

  obtain ⟨i₀, i₁, hI₀, hI₁, hi₀, hi₁, hcov', hglue', hmeet', -, -⟩ :=
    TwoAffineLineCover.baseChange (κ := κ) z j₀ j₁ hj₀ hj₁ hcov hglue hmeet

  haveI : IsClosedImmersion (Spec.map (CommRingCat.ofHom (algebraMap W k₀))) :=
    IsClosedImmersion.spec_of_surjective _ hq
  have hfac : Spec.map (CommRingCat.ofHom toκ) =
      Spec.map (CommRingCat.ofHom (algebraMap k₀ κ)) ≫ Spec.map (CommRingCat.ofHom (algebraMap W k₀)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hgalg, hg]
  have sq := isPullback_of_comp_mono z (Spec.map (CommRingCat.ofHom (algebraMap k₀ κ)))
    (Spec.map (CommRingCat.ofHom (algebraMap W k₀)))

  rw [hz, ← hfac] at sq
  let eI := sq.isoPullback
  have e_fst : eI.hom ≫ pullback.fst _ _ = pullback.fst _ _ := sq.isoPullback_hom_fst
  have e_snd : eI.hom ≫ pullback.snd _ _ = pullback.snd _ _ := sq.isoPullback_hom_snd
  refine ⟨i₀ ≫ eI.hom, i₁ ≫ eI.hom, inferInstance, inferInstance, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Category.assoc, e_snd, hi₀]
  · rw [Category.assoc, e_snd, hi₁]
  · have hsurj : Function.Surjective eI.hom.base := fun y =>
      ⟨eI.inv.base y, by rw [← TopCat.comp_app, ← Scheme.Hom.comp_base, Iso.inv_hom_id]; rfl⟩
    rw [Scheme.Hom.comp_base, Scheme.Hom.comp_base, TopCat.coe_comp, TopCat.coe_comp, Set.range_comp, Set.range_comp,
      ← Set.image_union, hcov', Set.image_univ, Set.range_eq_univ.mpr hsurj]
  · rw [← Category.assoc, hglue', Category.assoc]
  · have hinj : Function.Injective eI.hom.base := fun a b h => by
      have := congrArg eI.inv.base h
      rwa [← TopCat.comp_app, ← TopCat.comp_app, ← Scheme.Hom.comp_base, Iso.hom_inv_id] at this
    rw [Scheme.Hom.comp_base, Scheme.Hom.comp_base, TopCat.coe_comp, TopCat.coe_comp, Set.range_comp, Set.range_comp,
      ← Set.image_inter hinj, ← Category.assoc, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
    exact Set.image_mono hmeet'

end MvPolynomial.CrossingQuotient.Resolution
p2m_reactivate "P2MW.S_V3Asm_exc_rational.TwoAffineLineCover"
p2m_reactivate "P2MW.S_V3Asm_exc_rational.TwoAffineLineCover"
p2m_reactivate "P2MW.S_V3Asm_exc_rational.TwoAffineLineCover"

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_V3Asm_exc_rational.AlgebraicGeometry"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Scheme.IdealSheafData.le_ofIdeals_iff Surjective IsClosedImmersion.of_isPreimmersion Scheme.IdealSheafData.coe_support_vanishingIdeal Scheme.Hom Scheme.Pullback.range_fst Scheme.preimage_basicOpen Spec IsIntegral Scheme.IdealSheafData.range_subschemeι Spec.map Scheme Scheme.IdealSheafData.vanishingIdeal isClosed_singleton_iff_isClosedImmersion IsOpenImmersion Scheme.basicOpen_zero Scheme.Hom.comp_base IsReduced.of_openCover isIntegral_iff_irreducibleSpace_and_isReduced Scheme.Pullback.range_snd IsClosedImmersion.spec_of_surjective IsClosedImmersion IsReduced eq_zero_of_basicOpen_eq_bot IsClosedImmersion.lift Scheme.fromSpecResidueField_apply Etale IsClosedImmersion.lift_fac Scheme.IdealSheafData.ofIdealTop isReduced_of_isAffine_isReduced Scheme.IdealSheafData.ofIdeals isPullback_SpecMap_of_isPushout Scheme.Hom.comp_apply range_eq_univ Scheme.IdealSheafData Scheme.ΓSpecIso isIso_fiberToSpecResidueField_of_preimage_eq_singleton_of_isIso_residueFieldMap IsClosedImmersion.exists_iso_hom_comp_eq_of_range_eq"
p2m_open "AlgebraicGeometry"

section basechange

variable {X S S' S'' : Scheme.{u}} (f : X ⟶ S) (g' : S' ⟶ S) (g'' : S'' ⟶ S) (i : S'' ⟶ S') (hi : i ≫ g' = g'')

theorem isPullback_map_snd_snd :
    IsPullback (pullback.map f g'' f g' (𝟙 X) i (𝟙 S) (by simp) (by rw [Category.comp_id, hi]))
      (pullback.snd f g'') (pullback.snd f g') i := by
  refine IsPullback.of_right (h₁₂ := pullback.fst f g') (v₁₃ := f) (h₂₂ := g') ?_ ?_ (IsPullback.of_hasPullback f g')
  · rw [pullback.lift_fst, Category.comp_id, hi]
    exact IsPullback.of_hasPullback f g''
  · rw [pullback.lift_snd]

end basechange
p2m_reactivate "P2MW.S_V3Asm_exc_rational.TwoAffineLineCover"

section strict

variable {S Y X Xκ B Bκ R : Scheme.{u}}

theorem exists_iso_pullback_of_isClosedImmersion_of_preimage_range_eq
    (ιS : S ⟶ Y) (toDR : Y ⟶ X) (πX : X ⟶ B) (toBase : Y ⟶ B) (hbase : toDR ≫ πX = toBase)
    (b : Bκ ⟶ B) (p₁ : Xκ ⟶ X) (p₂ : Xκ ⟶ Bκ) (hP : IsPullback p₁ p₂ πX b)
    (c : R ⟶ Xκ) [IsClosedImmersion c] [IsReduced R] [IsClosedImmersion (ιS ≫ toDR)]
    (hrange : p₁.base ⁻¹' Set.range (ιS ≫ toDR).base = Set.range c.base)
    [IsReduced (pullback (ιS ≫ toBase) b)] :
    ∃ e : pullback (ιS ≫ toBase) b ⟶ R,
      IsIso e ∧ e ≫ c ≫ p₂ = pullback.snd _ _ ∧ e ≫ c ≫ p₁ = pullback.fst _ _ ≫ ιS ≫ toDR := by

  have hw : (pullback.fst (ιS ≫ toBase) b ≫ ιS ≫ toDR) ≫ πX = pullback.snd (ιS ≫ toBase) b ≫ b := by
    simp only [Category.assoc, hbase]
    exact pullback.condition
  let τ : pullback (ιS ≫ toBase) b ⟶ Xκ := hP.lift (pullback.fst _ _ ≫ ιS ≫ toDR) (pullback.snd _ _) hw
  have hτ₁ : τ ≫ p₁ = pullback.fst _ _ ≫ ιS ≫ toDR := hP.lift_fst _ _ _
  have hτ₂ : τ ≫ p₂ = pullback.snd _ _ := hP.lift_snd _ _ _

  let u : pullback (ιS ≫ toBase) b ⟶ pullback (ιS ≫ toDR) p₁ := pullback.lift (pullback.fst _ _) τ hτ₁.symm
  have hv : pullback.fst (ιS ≫ toDR) p₁ ≫ ιS ≫ toBase = (pullback.snd (ιS ≫ toDR) p₁ ≫ p₂) ≫ b := by
    rw [← hbase, Category.assoc, ← hP.w, ← Category.assoc (pullback.snd _ _), ← pullback.condition,
      Category.assoc, Category.assoc]
  let v : pullback (ιS ≫ toDR) p₁ ⟶ pullback (ιS ≫ toBase) b :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ p₂) hv
  have hvτ : v ≫ τ = pullback.snd (ιS ≫ toDR) p₁ := by
    apply hP.hom_ext
    · rw [Category.assoc, hτ₁, ← Category.assoc, pullback.lift_fst, pullback.condition]
    · rw [Category.assoc, hτ₂, pullback.lift_snd]
  have huv : u ≫ v = 𝟙 _ := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, Category.id_comp]
    · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, pullback.lift_snd, hτ₂, Category.id_comp]
  have hvu : v ≫ u = 𝟙 _ := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, Category.id_comp]
    · rw [Category.assoc, pullback.lift_snd, hvτ, Category.id_comp]
  haveI : IsIso u := ⟨⟨v, huv, hvu⟩⟩
  have hu : u ≫ pullback.snd (ιS ≫ toDR) p₁ = τ := pullback.lift_snd _ _ _

  haveI : IsClosedImmersion τ := by rw [← hu]; infer_instance
  have hsurj : Function.Surjective u.base := u.homeomorph.surjective
  have hτrange : Set.range τ.base = Set.range c.base := by
    rw [← hrange, ← hu, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      Set.range_eq_univ.mpr hsurj, Set.image_univ, Scheme.Pullback.range_snd]
  obtain ⟨e, he⟩ := IsClosedImmersion.exists_iso_hom_comp_eq_of_range_eq τ c hτrange
  exact ⟨e.hom, inferInstance, by rw [← Category.assoc, he, hτ₂], by rw [← Category.assoc, he, hτ₁]⟩

end strict
p2m_reactivate "P2MW.S_V3Asm_exc_rational.TwoAffineLineCover"

section chart

variable {U Se Res F : Scheme.{u}} (f : U ⟶ Se) (ρ : Res ⟶ Se) (lam : F ⟶ Res)

theorem pullback_fst_snd_comp_fst_eq :
    pullback.fst (pullback.snd f ρ) lam ≫ pullback.fst f ρ =
      (pullbackLeftPullbackSndIso f ρ lam).hom ≫ pullback.fst f (lam ≫ ρ) := by
  rw [pullbackLeftPullbackSndIso_hom_fst]

scoped instance isClosedImmersion_pullback_fst_snd_comp_fst [IsClosedImmersion (lam ≫ ρ)] :
    IsClosedImmersion (pullback.fst (pullback.snd f ρ) lam ≫ pullback.fst f ρ) := by
  rw [pullback_fst_snd_comp_fst_eq]
  infer_instance

theorem range_pullback_fst_snd_comp_fst :
    Set.range (pullback.fst (pullback.snd f ρ) lam ≫ pullback.fst f ρ).base =
      f.base ⁻¹' Set.range (lam ≫ ρ).base := by
  have hsurj : Function.Surjective (pullbackLeftPullbackSndIso f ρ lam).hom.base :=
    (pullbackLeftPullbackSndIso f ρ lam).hom.homeomorph.surjective
  rw [pullback_fst_snd_comp_fst_eq, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    Set.range_eq_univ.mpr hsurj, Set.image_univ, Scheme.Pullback.range_fst]

scoped instance etale_pullback_snd_snd [Etale f] : Etale (pullback.snd (pullback.snd f ρ) lam) := by
  have : pullback.snd (pullback.snd f ρ) lam = (pullbackLeftPullbackSndIso f ρ lam).hom ≫ pullback.snd f (lam ≫ ρ) := by
    rw [pullbackLeftPullbackSndIso_hom_snd]
  rw [this]
  infer_instance

end chart
p2m_reactivate "P2MW.S_V3Asm_exc_rational.TwoAffineLineCover"

end AlgebraicGeometry
p2m_reactivate "P2MW.S_V3Asm_exc_rational.TwoAffineLineCover P2MW.S_V3Asm_exc_rational.AlgebraicGeometry"

p2m_open "AlgebraicGeometry P2MW.S_V3Asm_exc_rational.AlgebraicGeometry CategoryTheory TopologicalSpace"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Scheme.IdealSheafData.le_ofIdeals_iff Surjective IsClosedImmersion.of_isPreimmersion Scheme.IdealSheafData.coe_support_vanishingIdeal Scheme.Hom Scheme.Pullback.range_fst Scheme.preimage_basicOpen Spec IsIntegral Scheme.IdealSheafData.range_subschemeι Spec.map Scheme Scheme.IdealSheafData.vanishingIdeal isClosed_singleton_iff_isClosedImmersion IsOpenImmersion Scheme.basicOpen_zero Scheme.Hom.comp_base IsReduced.of_openCover isIntegral_iff_irreducibleSpace_and_isReduced Scheme.Pullback.range_snd IsClosedImmersion.spec_of_surjective IsClosedImmersion IsReduced eq_zero_of_basicOpen_eq_bot IsClosedImmersion.lift Scheme.fromSpecResidueField_apply Etale IsClosedImmersion.lift_fac Scheme.IdealSheafData.ofIdealTop isReduced_of_isAffine_isReduced Scheme.IdealSheafData.ofIdeals isPullback_SpecMap_of_isPushout Scheme.Hom.comp_apply range_eq_univ Scheme.IdealSheafData Scheme.ΓSpecIso isIso_fiberToSpecResidueField_of_preimage_eq_singleton_of_isIso_residueFieldMap IsClosedImmersion.exists_iso_hom_comp_eq_of_range_eq"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "IdealSheafData.le_ofIdeals_iff fromSpecResidueField IdealSheafData.coe_support_vanishingIdeal Hom Γ Pullback.range_fst preimage_basicOpen IdealSheafData.range_subschemeι IdealSheafData.vanishingIdeal basicOpen_zero Hom.comp_base zeroLocus Pullback.range_snd residueField affineOpens basicOpen fromSpecResidueField_apply Opens residue IdealSheafData.ofIdealTop IdealSheafData.ofIdeals Hom.comp_apply IdealSheafData ΓSpecIso"
namespace IdealSheafData
p2m_export "AlgebraicGeometry.Scheme.IdealSheafData" "le_ofIdeals_iff radical coe_support_vanishingIdeal map subscheme range_subschemeι vanishingIdeal vanishingIdeal_ideal ideal map_comp subschemeι comap subschemeCover ofIdealTop ofIdeals support"
p2m_open "AlgebraicGeometry.Scheme.IdealSheafData AlgebraicGeometry.Scheme AlgebraicGeometry"

variable {X : Scheme.{u}}

theorem isReduced_Spec_of_isReduced (R : Type u) [CommRing R] [_root_.IsReduced R] :
    IsReduced (Spec (CommRingCat.of R)) := by
  haveI : _root_.IsReduced Γ(Spec (CommRingCat.of R), ⊤) :=
    isReduced_of_injective (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv
      (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv.injective
  exact isReduced_of_isAffine_isReduced _

theorem isReduced_subscheme_of_isRadical (I : X.IdealSheafData)
    (hI : ∀ U : X.affineOpens, (I.ideal U).IsRadical) : IsReduced I.subscheme := by
  haveI : ∀ i, IsReduced (I.subschemeCover.openCover.X i) := fun (U : X.affineOpens) => by
    change IsReduced (Spec (CommRingCat.of (Γ(X, (U : X.Opens)) ⧸ I.ideal U)))
    haveI : _root_.IsReduced (Γ(X, (U : X.Opens)) ⧸ I.ideal U) :=
      (Ideal.isRadical_iff_quotient_reduced _).mp (hI U)
    exact isReduced_Spec_of_isReduced _
  exact IsReduced.of_openCover _ I.subschemeCover.openCover

scoped instance isReduced_subscheme_vanishingIdeal (Z : Closeds X) : IsReduced (vanishingIdeal Z).subscheme :=
  isReduced_subscheme_of_isRadical _ fun U => by
    rw [vanishingIdeal_ideal]
    exact PrimeSpectrum.isRadical_vanishingIdeal _

theorem isIntegral_subscheme_vanishingIdeal_closure_singleton (x : X) :
    IsIntegral (vanishingIdeal ⟨closure {x}, isClosed_closure⟩).subscheme := by
  set I : X.IdealSheafData := vanishingIdeal ⟨closure {x}, isClosed_closure⟩
  have hsupp : (I.support : Set X) = closure {x} := by
    rw [coe_support_vanishingIdeal]; rfl

  have hx : x ∈ Set.range I.subschemeι.base := by
    rw [range_subschemeι, hsupp]; exact subset_closure rfl
  obtain ⟨s, hs⟩ := hx

  have hind : Topology.IsInducing I.subschemeι.base := I.subschemeι.isClosedEmbedding.isInducing
  have hgen : closure ({s} : Set I.subscheme) = Set.univ := by
    rw [hind.closure_eq_preimage_closure_image, Set.image_singleton, hs, ← hsupp, ← range_subschemeι,
      Set.preimage_range]
  haveI : IrreducibleSpace I.subscheme := by
    rw [irreducibleSpace_def, Set.top_eq_univ, ← hgen]
    exact isIrreducible_singleton.closure
  exact (isIntegral_iff_irreducibleSpace_and_isReduced _).mpr ⟨inferInstance, inferInstance⟩

end AlgebraicGeometry.Scheme.IdealSheafData
p2m_reactivate "P2MW.S_V3Asm_exc_rational.TwoAffineLineCover P2MW.S_V3Asm_exc_rational.AlgebraicGeometry P2MW.S_V3Asm_exc_rational.AlgebraicGeometry.Scheme P2MW.S_V3Asm_exc_rational.AlgebraicGeometry.Scheme.IdealSheafData"
p2m_reactivate "P2MW.S_V3Asm_exc_rational.TwoAffineLineCover P2MW.S_V3Asm_exc_rational.AlgebraicGeometry P2MW.S_V3Asm_exc_rational.AlgebraicGeometry.Scheme"
p2m_reactivate "P2MW.S_V3Asm_exc_rational.TwoAffineLineCover P2MW.S_V3Asm_exc_rational.AlgebraicGeometry"

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_V3Asm_exc_rational.AlgebraicGeometry"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Scheme.IdealSheafData.le_ofIdeals_iff Surjective IsClosedImmersion.of_isPreimmersion Scheme.IdealSheafData.coe_support_vanishingIdeal Scheme.Hom Scheme.Pullback.range_fst Scheme.preimage_basicOpen Spec IsIntegral Scheme.IdealSheafData.range_subschemeι Spec.map Scheme Scheme.IdealSheafData.vanishingIdeal isClosed_singleton_iff_isClosedImmersion IsOpenImmersion Scheme.basicOpen_zero Scheme.Hom.comp_base IsReduced.of_openCover isIntegral_iff_irreducibleSpace_and_isReduced Scheme.Pullback.range_snd IsClosedImmersion.spec_of_surjective IsClosedImmersion IsReduced eq_zero_of_basicOpen_eq_bot IsClosedImmersion.lift Scheme.fromSpecResidueField_apply Etale IsClosedImmersion.lift_fac Scheme.IdealSheafData.ofIdealTop isReduced_of_isAffine_isReduced Scheme.IdealSheafData.ofIdeals isPullback_SpecMap_of_isPushout Scheme.Hom.comp_apply range_eq_univ Scheme.IdealSheafData Scheme.ΓSpecIso isIso_fiberToSpecResidueField_of_preimage_eq_singleton_of_isIso_residueFieldMap IsClosedImmersion.exists_iso_hom_comp_eq_of_range_eq"
p2m_open "AlgebraicGeometry"

section

variable {E F B Bκ : Scheme.{u}} (sE : E ⟶ B) (sF : F ⟶ B) (φ : E ≅ F) (hφ : φ.hom ≫ sF = sE) (b : Bκ ⟶ B)

noncomputable def pullbackIsoOfIsoOver : pullback sE b ≅ pullback sF b :=
  pullback.congrHom hφ.symm rfl ≪≫ (pullbackRightPullbackFstIso sF b φ.hom).symm ≪≫
    asIso (pullback.snd φ.hom (pullback.fst sF b))

@[reassoc]
theorem pullbackIsoOfIsoOver_hom_snd :
    (pullbackIsoOfIsoOver sE sF φ hφ b).hom ≫ pullback.snd sF b = pullback.snd sE b := by
  simp only [pullbackIsoOfIsoOver, Iso.trans_hom, Iso.symm_hom, asIso_hom, Category.assoc,
    pullbackRightPullbackFstIso_inv_snd_snd, pullback.congrHom_hom, pullback.lift_snd, Category.comp_id]

@[reassoc]
theorem pullbackIsoOfIsoOver_hom_fst :
    (pullbackIsoOfIsoOver sE sF φ hφ b).hom ≫ pullback.fst sF b = pullback.fst sE b ≫ φ.hom := by
  simp only [pullbackIsoOfIsoOver, Iso.trans_hom, Iso.symm_hom, asIso_hom, Category.assoc]
  rw [← pullback.condition, pullbackRightPullbackFstIso_inv_fst_assoc, pullback.congrHom_hom, pullback.lift_fst_assoc,
    Category.comp_id]

end
p2m_reactivate "P2MW.S_V3Asm_exc_rational.TwoAffineLineCover P2MW.S_V3Asm_exc_rational.AlgebraicGeometry P2MW.S_V3Asm_exc_rational.AlgebraicGeometry.Scheme P2MW.S_V3Asm_exc_rational.AlgebraicGeometry.Scheme.IdealSheafData"

theorem exists_iso_pullback_of_iso_over {E F B Bκ MC : Scheme.{u}} (sE : E ⟶ B) (sF : F ⟶ B) (b : Bκ ⟶ B)
    (φ : E ≅ F) (hφ : φ.hom ≫ sF = sE) (tM : MC ⟶ Bκ)
    (e : MC ≅ pullback sF b) (he : e.hom ≫ pullback.snd sF b = tM) :
    ∃ e' : MC ⟶ pullback sE b, IsIso e' ∧ e' ≫ pullback.snd sE b = tM := by
  refine ⟨e.hom ≫ (pullbackIsoOfIsoOver sE sF φ hφ b).inv, inferInstance, ?_⟩
  rw [Category.assoc, ← he]
  congr 1
  rw [Iso.inv_comp_eq, pullbackIsoOfIsoOver_hom_snd]

section liftOfIsIso

variable {F Res Yn : Scheme.{u}} (i : F ⟶ Res) (g : Yn ⟶ Res) [IsIso (pullback.fst i g)]

noncomputable def liftOfIsIso : F ⟶ Yn := inv (pullback.fst i g) ≫ pullback.snd i g

@[reassoc (attr := simp)]
theorem liftOfIsIso_comp : liftOfIsIso i g ≫ g = i := by
  rw [liftOfIsIso, Category.assoc, ← pullback.condition, IsIso.inv_hom_id_assoc]

scoped instance [IsClosedImmersion i] : IsClosedImmersion (liftOfIsIso i g) := by
  haveI : IsClosedImmersion (pullback.snd i g) := MorphismProperty.pullback_snd (P := @IsClosedImmersion) _ _ inferInstance
  rw [liftOfIsIso]; infer_instance

theorem range_liftOfIsIso : Set.range (liftOfIsIso i g).base = g.base ⁻¹' Set.range i.base := by
  have hsurj : Function.Surjective (inv (pullback.fst i g)).base := (inv (pullback.fst i g)).homeomorph.surjective
  rw [liftOfIsIso, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Set.range_eq_univ.mpr hsurj, Set.image_univ,
    Scheme.Pullback.range_snd]

end liftOfIsIso
p2m_reactivate "P2MW.S_V3Asm_exc_rational.TwoAffineLineCover P2MW.S_V3Asm_exc_rational.AlgebraicGeometry P2MW.S_V3Asm_exc_rational.AlgebraicGeometry.Scheme P2MW.S_V3Asm_exc_rational.AlgebraicGeometry.Scheme.IdealSheafData"

theorem exists_iso_of_range_eq_image {E F Yn Y : Scheme.{u}} (ιE : E ⟶ Y) [IsClosedImmersion ιE] [IsReduced E]
    (lam' : F ⟶ Yn) [IsClosedImmersion lam'] [IsReduced F] (ι : Yn ⟶ Y) [IsOpenImmersion ι]
    (hrange : Set.range ιE.base = ι.base '' Set.range lam'.base) :
    ∃ φ : E ≅ F, φ.hom ≫ lam' ≫ ι = ιE := by
  have hr : Set.range (lam' ≫ ι).base = Set.range ιE.base := by
    rw [hrange, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
  haveI : IsClosedImmersion (lam' ≫ ι) :=
    IsClosedImmersion.of_isPreimmersion _ (hr ▸ ιE.isClosedEmbedding.isClosed_range)
  exact IsClosedImmersion.exists_iso_hom_comp_eq_of_range_eq ιE (lam' ≫ ι) hr.symm

end AlgebraicGeometry
p2m_reactivate "P2MW.S_V3Asm_exc_rational.TwoAffineLineCover P2MW.S_V3Asm_exc_rational.AlgebraicGeometry P2MW.S_V3Asm_exc_rational.AlgebraicGeometry.Scheme P2MW.S_V3Asm_exc_rational.AlgebraicGeometry.Scheme.IdealSheafData"

noncomputable section

namespace V3Glue
p2m_export "V3Glue" "Site.Node Aux.Layer0.W6.isIso_pullback_fst_of_over_point ChartInput.vertex_def ChartInput"
namespace ChartInput
p2m_export "V3Glue.ChartInput" "ηG_inr compG coe_support_compG preimage_g_closure_singleton preimage_ιY_closure_singleton_exPt xU vertex vertex_def f_apply_eq_iff ε exPt toDR_eq_of_mem_closure_exPt Y q a j toGlueInput hq g toB toB_eq πX Res X0 U S one_le_thick B ρ x thick x_mem_U f"
p2m_open "V3Glue.ChartInput V3Glue"

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_V3Asm_exc_rational.AlgebraicGeometry TopologicalSpace"

variable {X : Scheme.{0}} {N : Type} (C : ChartInput X N)

private theorem _root_.V3Glue.ChartInput.exc_rational_of
    (hRF : ∀ n, IsIso ((C.f n).residueFieldMap (C.xU n)))
    (gRes : ∀ n, Fin (C.thick n - 1) → C.Res n) (hgRes : ∀ n k, C.ρ n (gRes n k) = C.vertex n)
    (ξ : Fin 2 → X) (hξ : ∀ j, ξ j ∈ C.X0)
    (n : N) (k : Fin (C.thick n - 1)) (hx : IsClosed ({C.x n} : Set X))

    (L : (C.Res n).IdealSheafData) [IsReduced L.subscheme]
    (hLsupp : (L.support : Set (C.Res n)) = closure {gRes n k})
    (hcl : closure ({gRes n k} : Set (C.Res n)) ⊆ (C.ρ n).base ⁻¹' {C.vertex n})
    (lam' : L.subscheme ⟶ C.Y n) [IsClosedImmersion lam']
    (hrange' : Set.range lam'.base = (C.g n).base ⁻¹' (L.support : Set (C.Res n)))

    {Bκ MC : Scheme.{0}} (b : Bκ ⟶ C.B) (sF : L.subscheme ⟶ C.B) (hsF : lam' ≫ C.toB n = sF)
    (tM : MC ⟶ Bκ) (e : MC ≅ pullback sF b) (he : e.hom ≫ pullback.snd sF b = tM) :
    ∃ e' : MC ⟶ pullback ((C.compG hRF gRes hgRes ξ hξ (Sum.inr ⟨n, k⟩)).subschemeι ≫ C.toGlueInput.toDR ≫ C.πX) b,
      IsIso e' ∧ e' ≫ pullback.snd _ _ = tM := by

  have hE1 : closure {C.exPt n (hRF n) (gRes n k) (hgRes n k)} ⊆ Set.range (C.toGlueInput.ιY n).base := by
    intro y hy
    rw [C.toGlueInput.range_ιY C.hq n]
    show C.toGlueInput.toDR.base y ∈ (C.U n : Set X)
    rw [C.toDR_eq_of_mem_closure_exPt n (hRF n) hx (gRes n k) (hgRes n k) hy]
    exact C.x_mem_U n
  have hrange : Set.range (C.compG hRF gRes hgRes ξ hξ (Sum.inr ⟨n, k⟩)).subschemeι.base =
      (C.toGlueInput.ιY n).base '' Set.range lam'.base := by
    rw [Scheme.IdealSheafData.range_subschemeι, coe_support_compG, ηG_inr]
    erw [hrange', hLsupp, C.preimage_g_closure_singleton n (hRF n) (gRes n k) (hgRes n k) hcl,
      ← C.preimage_ιY_closure_singleton_exPt n (hRF n) (gRes n k) (hgRes n k),
      Set.image_preimage_eq_inter_range, Set.inter_eq_left.mpr hE1]

  haveI : IsReduced (C.compG hRF gRes hgRes ξ hξ (Sum.inr ⟨n, k⟩)).subscheme := by
    unfold compG; infer_instance
  have hopen : IsOpenImmersion (C.toGlueInput.ιY n) := inferInstance
  have hredE : IsReduced (C.compG hRF gRes hgRes ξ hξ (Sum.inr ⟨n, k⟩)).subscheme := inferInstance
  obtain ⟨φ, hφ0⟩ := @AlgebraicGeometry.exists_iso_of_range_eq_image _ _ _ _
    (C.compG hRF gRes hgRes ξ hξ (Sum.inr ⟨n, k⟩)).subschemeι inferInstance hredE lam' inferInstance inferInstance
    (C.toGlueInput.ιY n) hopen hrange

  have h2' : C.toGlueInput.ιY n ≫ C.toGlueInput.toDR = C.q n ≫ (C.U n).ι := C.toGlueInput.ιY_toDR n
  have E1 : φ.hom ≫ sF = φ.hom ≫ (lam' ≫ C.toB n) := by rw [hsF]
  have E2 : φ.hom ≫ (lam' ≫ C.toB n) = φ.hom ≫ (lam' ≫ ((C.q n ≫ (C.U n).ι) ≫ C.πX)) := by
    rw [C.toB_eq]; rfl
  have E3 : φ.hom ≫ (lam' ≫ ((C.q n ≫ (C.U n).ι) ≫ C.πX)) =
      φ.hom ≫ (lam' ≫ ((C.toGlueInput.ιY n ≫ C.toGlueInput.toDR) ≫ C.πX)) :=
    congrArg (fun m => φ.hom ≫ (lam' ≫ (m ≫ C.πX))) h2'.symm
  have E4 : φ.hom ≫ (lam' ≫ ((C.toGlueInput.ιY n ≫ C.toGlueInput.toDR) ≫ C.πX)) =
      ((φ.hom ≫ lam' ≫ C.toGlueInput.ιY n) ≫ C.toGlueInput.toDR) ≫ C.πX := by
    simp only [Category.assoc]
  have E5 : ((φ.hom ≫ lam' ≫ C.toGlueInput.ιY n) ≫ C.toGlueInput.toDR) ≫ C.πX =
      (C.compG hRF gRes hgRes ξ hξ (Sum.inr ⟨n, k⟩)).subschemeι ≫ C.toGlueInput.toDR ≫ C.πX := by
    rw [hφ0, Category.assoc]
  have hφ : φ.hom ≫ sF = (C.compG hRF gRes hgRes ξ hξ (Sum.inr ⟨n, k⟩)).subschemeι ≫ C.toGlueInput.toDR ≫ C.πX :=
    E1.trans (E2.trans (E3.trans (E4.trans E5)))
  exact AlgebraicGeometry.exists_iso_pullback_of_iso_over _ sF b φ hφ tM e he

p2m_export "V3Glue.ChartInput" "exc_rational_of"
end V3Glue.ChartInput
p2m_reactivate "P2MW.S_V3Asm_exc_rational.TwoAffineLineCover P2MW.S_V3Asm_exc_rational.AlgebraicGeometry P2MW.S_V3Asm_exc_rational.AlgebraicGeometry.Scheme P2MW.S_V3Asm_exc_rational.AlgebraicGeometry.Scheme.IdealSheafData"
p2m_reactivate "P2MW.S_V3Asm_exc_rational.TwoAffineLineCover P2MW.S_V3Asm_exc_rational.AlgebraicGeometry P2MW.S_V3Asm_exc_rational.AlgebraicGeometry.Scheme P2MW.S_V3Asm_exc_rational.AlgebraicGeometry.Scheme.IdealSheafData"

end
p2m_reactivate "P2MW.S_V3Asm_exc_rational.TwoAffineLineCover P2MW.S_V3Asm_exc_rational.AlgebraicGeometry P2MW.S_V3Asm_exc_rational.AlgebraicGeometry.Scheme P2MW.S_V3Asm_exc_rational.AlgebraicGeometry.Scheme.IdealSheafData"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Scheme.IdealSheafData.le_ofIdeals_iff Surjective IsClosedImmersion.of_isPreimmersion Scheme.IdealSheafData.coe_support_vanishingIdeal Scheme.Hom Scheme.Pullback.range_fst Scheme.preimage_basicOpen Spec IsIntegral Scheme.IdealSheafData.range_subschemeι Spec.map Scheme Scheme.IdealSheafData.vanishingIdeal isClosed_singleton_iff_isClosedImmersion IsOpenImmersion Scheme.basicOpen_zero Scheme.Hom.comp_base IsReduced.of_openCover isIntegral_iff_irreducibleSpace_and_isReduced Scheme.Pullback.range_snd IsClosedImmersion.spec_of_surjective IsClosedImmersion IsReduced eq_zero_of_basicOpen_eq_bot IsClosedImmersion.lift Scheme.fromSpecResidueField_apply Etale IsClosedImmersion.lift_fac Scheme.IdealSheafData.ofIdealTop isReduced_of_isAffine_isReduced Scheme.IdealSheafData.ofIdeals isPullback_SpecMap_of_isPushout Scheme.Hom.comp_apply range_eq_univ Scheme.IdealSheafData Scheme.ΓSpecIso isIso_fiberToSpecResidueField_of_preimage_eq_singleton_of_isIso_residueFieldMap IsClosedImmersion.exists_iso_hom_comp_eq_of_range_eq"
p2m_open "AlgebraicGeometry"

theorem exists_lift_fromSpecResidueField_of_isReduced {Y S : Scheme.{u}} (h : Y ⟶ S) [IsReduced Y]
    (s : S) (hs : IsClosed ({s} : Set S)) (hr : Set.range h.base ⊆ {s}) :
    ∃ t : Y ⟶ Spec (S.residueField s), t ≫ S.fromSpecResidueField s = h := by
  haveI : IsClosedImmersion (S.fromSpecResidueField s) := isClosed_singleton_iff_isClosedImmersion.mp hs
  refine ⟨IsClosedImmersion.lift (S.fromSpecResidueField s) h ?_, IsClosedImmersion.lift_fac _ _ _⟩

  change (S.fromSpecResidueField s).ker ≤ Scheme.IdealSheafData.ofIdeals fun U => RingHom.ker (h.app U).hom
  rw [Scheme.IdealSheafData.le_ofIdeals_iff]
  intro U a ha
  change a ∈ RingHom.ker (h.app U).hom
  have ha0 : (S.fromSpecResidueField s).app U a = 0 := (S.fromSpecResidueField s).ideal_ker_le U ha

  have hs' : s ∉ S.basicOpen a := by
    intro hmem
    have : IsLocalRing.closedPoint (S.residueField s) ∈ (S.fromSpecResidueField s) ⁻¹ᵁ S.basicOpen a := by
      show (S.fromSpecResidueField s).base _ ∈ S.basicOpen a
      rwa [Scheme.fromSpecResidueField_apply]
    rw [Scheme.preimage_basicOpen, ha0, Scheme.basicOpen_zero] at this
    exact this

  refine RingHom.mem_ker.mpr (eq_zero_of_basicOpen_eq_bot _ ?_)
  rw [← Scheme.preimage_basicOpen, eq_bot_iff]
  intro y hy
  exact absurd ((hr ⟨y, rfl⟩ : h.base y = s) ▸ (hy : h.base y ∈ S.basicOpen a)) hs'

end AlgebraicGeometry
p2m_reactivate "P2MW.S_V3Asm_exc_rational.TwoAffineLineCover P2MW.S_V3Asm_exc_rational.AlgebraicGeometry P2MW.S_V3Asm_exc_rational.AlgebraicGeometry.Scheme P2MW.S_V3Asm_exc_rational.AlgebraicGeometry.Scheme.IdealSheafData"

namespace V3Glue
p2m_export "V3Glue" "Site.Node Aux.Layer0.W6.isIso_pullback_fst_of_over_point ChartInput.vertex_def ChartInput"
namespace ChartInput
p2m_export "V3Glue.ChartInput" "ηG_inr compG coe_support_compG preimage_g_closure_singleton preimage_ιY_closure_singleton_exPt xU vertex vertex_def f_apply_eq_iff ε exPt toDR_eq_of_mem_closure_exPt Y q a j toGlueInput hq g toB toB_eq πX Res X0 U S one_le_thick B ρ x thick x_mem_U f"
p2m_open "V3Glue.ChartInput V3Glue"

variable {X : Scheme.{0}} {N : Type} (C : ChartInput X N) (n : N)

private theorem _root_.V3Glue.ChartInput.isIso_pullback_fst_subschemeι_g
    (hv : IsClosed ({C.vertex n} : Set (C.S n)))
    (hfib : IsIso ((C.f n).fiberToSpecResidueField (C.vertex n)))
    (L : (C.Res n).IdealSheafData) [IsReduced L.subscheme]
    (hL : (L.support : Set (C.Res n)) ⊆ (C.ρ n).base ⁻¹' {C.vertex n}) :
    IsIso (pullback.fst L.subschemeι (C.g n)) := by
  have hr : Set.range (L.subschemeι ≫ C.ρ n).base ⊆ {C.vertex n} := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply]
    exact hL (L.range_subschemeι ▸ Set.mem_range_self z)
  obtain ⟨t, ht⟩ := AlgebraicGeometry.exists_lift_fromSpecResidueField_of_isReduced (L.subschemeι ≫ C.ρ n)
    (C.vertex n) hv hr
  exact V3Glue.Aux.Layer0.W6.isIso_pullback_fst_of_over_point (C.f n) (C.ρ n) (C.xU n) hfib L.subschemeι t ht.symm

p2m_export "V3Glue.ChartInput" "isIso_pullback_fst_subschemeι_g"
end V3Glue.ChartInput
p2m_reactivate "P2MW.S_V3Asm_exc_rational.TwoAffineLineCover P2MW.S_V3Asm_exc_rational.AlgebraicGeometry P2MW.S_V3Asm_exc_rational.AlgebraicGeometry.Scheme P2MW.S_V3Asm_exc_rational.AlgebraicGeometry.Scheme.IdealSheafData"
p2m_reactivate "P2MW.S_V3Asm_exc_rational.TwoAffineLineCover P2MW.S_V3Asm_exc_rational.AlgebraicGeometry P2MW.S_V3Asm_exc_rational.AlgebraicGeometry.Scheme P2MW.S_V3Asm_exc_rational.AlgebraicGeometry.Scheme.IdealSheafData"

noncomputable section

namespace V3Asm
p2m_export "V3Asm" "πX SiteHyps R C D Y toDR toBase hq width hRF p_mem_maximalIdeal ξ vertex_eq gRes hgRes comp"
p2m_open "V3Asm"

p2m_open "ModularCurve MvPolynomial P2MW.S_V3Asm_exc_rational.MvPolynomial MvPolynomial.CrossingQuotient P2MW.S_V3Asm_exc_rational.MvPolynomial.CrossingQuotient"

variable (p : ℕ) [Fact p.Prime] (𝔛 : DRModelPackage p) (O : Type) [CommRing O] [IsDomain O]
  [IsDiscreteValuationRing O] (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)})
  (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ] (toκ : O →+* κ)
  (H : SiteHyps p 𝔛 O κ toκ) (hξ : ∀ j, ξ p 𝔛 O κ toκ j ∈ (C p 𝔛 O κ toκ hϖ H).X0)

include p 𝔛 O hϖ κ toκ H hξ

theorem etale_f' (n : V3Glue.Site.Node p 𝔛 κ) : Etale ((C p 𝔛 O κ toκ hϖ H).f n) := by
  haveI := H.nodeFinite
  exact (R p 𝔛 O κ toκ hϖ H).etale_toChartInput_f ((R p 𝔛 O κ toκ hϖ H).hnbhd_of H.ET) n

theorem isClosed_vertex (n : V3Glue.Site.Node p 𝔛 κ) :
    IsClosed ({(C p 𝔛 O κ toκ hϖ H).vertex n} : Set ((C p 𝔛 O κ toκ hϖ H).S n)) := by
  rw [vertex_eq p 𝔛 O κ toκ hϖ H n]
  exact (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mpr
    (MvPolynomial.CrossingQuotient.isMaximal_vertexIdeal ((p : ℕ) : O) (IsLocalRing.maximalIdeal O)
      (p_mem_maximalIdeal p O hϖ) ((C p 𝔛 O κ toκ hϖ H).thick n) ((C p 𝔛 O κ toκ hϖ H).one_le_thick n))

theorem hfib (n : V3Glue.Site.Node p 𝔛 κ) :
    IsIso (((C p 𝔛 O κ toκ hϖ H).f n).fiberToSpecResidueField ((C p 𝔛 O κ toκ hϖ H).vertex n)) := by
  haveI := etale_f' p 𝔛 O hϖ κ toκ H hξ n
  haveI := hRF p 𝔛 O κ toκ hϖ H n
  rw [V3Glue.ChartInput.vertex_def]
  exact AlgebraicGeometry.isIso_fiberToSpecResidueField_of_preimage_eq_singleton_of_isIso_residueFieldMap
    ((C p 𝔛 O κ toκ hϖ H).f n) ((C p 𝔛 O κ toκ hϖ H).xU n)
    (fun y h => ((C p 𝔛 O κ toκ hϖ H).f_apply_eq_iff n y).mp h)

omit hξ in

abbrev Fa (e : ℕ) (k : Fin (e + 1)) : (Resolution ((p : ℕ) : O) e).IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal ⟨closure
    ((⋃ (j : Fin e) (_ : (j : ℕ) + 1 = (k : ℕ)), (Resolution.ι ((p : ℕ) : O) e j) '' (PrimeSpectrum.zeroLocus {CrossingQuotient.U ((p : ℕ) : O)})) ∪
     (⋃ (j : Fin e) (_ : (j : ℕ) = (k : ℕ)), (Resolution.ι ((p : ℕ) : O) e j) '' (PrimeSpectrum.zeroLocus {CrossingQuotient.V ((p : ℕ) : O)}))),
    isClosed_closure⟩

theorem hFa (e : ℕ) : ∀ (i : Fin e) (k : Fin (e + 1)), (Fa p O e k).comap (Resolution.ι ((p : ℕ) : O) e i) =
    Scheme.IdealSheafData.ofIdealTop (Ideal.map (Scheme.ΓSpecIso (CommRingCat.of (CrossingQuotient O ((p : ℕ) : O)))).inv.hom
      (if (k : ℕ) = (i : ℕ) then Ideal.span {CrossingQuotient.V ((p : ℕ) : O)}
        else if (k : ℕ) = (i : ℕ) + 1 then Ideal.span {CrossingQuotient.U ((p : ℕ) : O)} else ⊤)) := by
  haveI : IsReduced (O ⧸ Ideal.span {((p : ℕ) : O)}) := by rw [← hϖ]; infer_instance
  intro i k
  exact MvPolynomial.CrossingQuotient.Resolution.comap_iota_vanishingIdeal_closure_lines ((p : ℕ) : O) e i (k : ℕ)

theorem closure_lines_eq (e : ℕ) (k : Fin e) (hk : 0 < (k : ℕ)) :
    closure ((⋃ (j : Fin e) (_ : (j : ℕ) + 1 = (k : ℕ)), (Resolution.ι ((p : ℕ) : O) e j) '' (PrimeSpectrum.zeroLocus {CrossingQuotient.U ((p : ℕ) : O)})) ∪
      (⋃ (j : Fin e) (_ : (j : ℕ) = (k : ℕ)), (Resolution.ι ((p : ℕ) : O) e j) '' (PrimeSpectrum.zeroLocus {CrossingQuotient.V ((p : ℕ) : O)}))) =
    closure {Resolution.lineGen ((p : ℕ) : O) e (IsLocalRing.maximalIdeal O) (p_mem_maximalIdeal p O hϖ) k} := by

  have hUle : ∀ Q : PrimeSpectrum (CrossingQuotient O ((p : ℕ) : O)), CrossingQuotient.U ((p : ℕ) : O) ∈ Q.asIdeal →
      lineUIdeal ((p : ℕ) : O) (IsLocalRing.maximalIdeal O) (p_mem_maximalIdeal p O hϖ) ≤ Q.asIdeal := by
    intro Q hU
    rw [lineUIdeal_le_iff]
    refine ⟨hU, fun w hw => ?_⟩
    rw [hϖ, Ideal.mem_span_singleton] at hw
    obtain ⟨c, rfl⟩ := hw
    rw [map_mul, ← CrossingQuotient.U_mul_V]
    exact Q.asIdeal.mul_mem_right _ (Q.asIdeal.mul_mem_right _ hU)
  have hVle : ∀ Q : PrimeSpectrum (CrossingQuotient O ((p : ℕ) : O)), CrossingQuotient.V ((p : ℕ) : O) ∈ Q.asIdeal →
      lineVIdeal ((p : ℕ) : O) (IsLocalRing.maximalIdeal O) (p_mem_maximalIdeal p O hϖ) ≤ Q.asIdeal := by
    intro Q hV
    rw [lineVIdeal_le_iff]
    refine ⟨hV, fun w hw => ?_⟩
    rw [hϖ, Ideal.mem_span_singleton] at hw
    obtain ⟨c, rfl⟩ := hw
    rw [map_mul, ← CrossingQuotient.U_mul_V]
    exact Q.asIdeal.mul_mem_right _ (Q.asIdeal.mul_mem_left _ hV)
  apply le_antisymm
  · refine closure_minimal ?_ isClosed_closure
    rintro z (hz | hz)
    · simp only [Set.mem_iUnion, Set.mem_image] at hz
      obtain ⟨j, hj, Q, hQ, rfl⟩ := hz
      exact (Resolution.mem_closure_lineGen_iff ((p : ℕ) : O) e (IsLocalRing.maximalIdeal O) (p_mem_maximalIdeal p O hϖ) k _).mpr
        (Or.inr ⟨j, Q, hj, hUle Q (hQ (Set.mem_singleton _)), rfl⟩)
    · simp only [Set.mem_iUnion, Set.mem_image] at hz
      obtain ⟨j, hj, Q, hQ, rfl⟩ := hz
      have hjk : j = k := Fin.ext hj
      subst hjk
      exact (Resolution.mem_closure_lineGen_iff ((p : ℕ) : O) e (IsLocalRing.maximalIdeal O) (p_mem_maximalIdeal p O hϖ) j _).mpr
        (Or.inl ⟨Q, hVle Q (hQ (Set.mem_singleton _)), rfl⟩)
  · refine closure_mono ?_
    rw [Set.singleton_subset_iff]
    refine Or.inr ?_
    simp only [Set.mem_iUnion, Set.mem_image]
    refine ⟨k, rfl, ⟨lineVIdeal ((p : ℕ) : O) (IsLocalRing.maximalIdeal O) (p_mem_maximalIdeal p O hϖ), inferInstance⟩, ?_, ?_⟩
    · exact Set.singleton_subset_iff.mpr (V_mem_lineVIdeal ((p : ℕ) : O) (IsLocalRing.maximalIdeal O) (p_mem_maximalIdeal p O hϖ))
    · rfl

theorem coe_support_Fa (n : V3Glue.Site.Node p 𝔛 κ) (i : Fin (width p 𝔛 O κ toκ hϖ H n - 1)) :
    ((Fa p O ((C p 𝔛 O κ toκ hϖ H).thick n) ⟨(i : ℕ) + 1, (by have := i.2; dsimp only [width] at this; omega)⟩).support :
        Set (Resolution ((p : ℕ) : O) ((C p 𝔛 O κ toκ hϖ H).thick n))) =
      closure {gRes p 𝔛 O κ toκ hϖ H n i} := by
  rw [Scheme.IdealSheafData.coe_support_vanishingIdeal]
  have hk : (i : ℕ) + 1 < (C p 𝔛 O κ toκ hϖ H).thick n := by have := i.2; dsimp only [width] at this; omega
  show closure _ = closure {Resolution.lineUGen _ _ _ _ _}
  rw [Resolution.lineUGen_eq_lineGen_succ _ _ _ _ _ hk]
  exact closure_lines_eq p 𝔛 O hϖ κ toκ H hξ ((C p 𝔛 O κ toκ hϖ H).thick n) ⟨(i : ℕ) + 1, hk⟩ (Nat.succ_pos _)

theorem closure_gRes_subset (n : V3Glue.Site.Node p 𝔛 κ) (i : Fin (width p 𝔛 O κ toκ hϖ H n - 1)) :
    closure ({gRes p 𝔛 O κ toκ hϖ H n i} : Set ((C p 𝔛 O κ toκ hϖ H).Res n)) ⊆
      ((C p 𝔛 O κ toκ hϖ H).ρ n).base ⁻¹' {(C p 𝔛 O κ toκ hϖ H).vertex n} := by
  refine closure_minimal ?_ ((isClosed_vertex p 𝔛 O hϖ κ toκ H hξ n).preimage ((C p 𝔛 O κ toκ hϖ H).ρ n).continuous)
  rintro _ rfl
  exact hgRes p 𝔛 O κ toκ hϖ H n i

theorem exc_rational (n : V3Glue.Site.Node p 𝔛 κ) (i : Fin (width p 𝔛 O κ toκ hϖ H n - 1)) :
    ∃ (M : AlgebraicCurve.CurveModel κ (RatFunc κ))
      (e : M.C ⟶ pullback ((comp p 𝔛 O κ toκ hϖ H hξ (Sum.inr ⟨n, i⟩)).subschemeι ≫ toBase p 𝔛 O κ toκ hϖ H)
        (Spec.map (CommRingCat.ofHom toκ))),
      IsIso e ∧ e ≫ pullback.snd _ _ = M.toBase := by
  unfold toBase toDR D comp
  have hk : (i : ℕ) + 1 < (C p 𝔛 O κ toκ hϖ H).thick n := by have := i.2; dsimp only [width] at this; omega

  set L : ((C p 𝔛 O κ toκ hϖ H).Res n).IdealSheafData :=
    Fa p O ((C p 𝔛 O κ toκ hϖ H).thick n) ⟨(i : ℕ) + 1, by omega⟩ with hL
  haveI : IsReduced L.subscheme := Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal _
  have hLsupp : (L.support : Set ((C p 𝔛 O κ toκ hϖ H).Res n)) = closure {gRes p 𝔛 O κ toκ hϖ H n i} :=
    coe_support_Fa p 𝔛 O hϖ κ toκ H hξ n i
  have hcl := closure_gRes_subset p 𝔛 O hϖ κ toκ H hξ n i

  haveI hiso : IsIso (pullback.fst L.subschemeι ((C p 𝔛 O κ toκ hϖ H).g n)) :=
    (C p 𝔛 O κ toκ hϖ H).isIso_pullback_fst_subschemeι_g n (isClosed_vertex p 𝔛 O hϖ κ toκ H hξ n)
      (hfib p 𝔛 O hϖ κ toκ H hξ n) L (by rw [hLsupp]; exact hcl)

  letI : Field (O ⧸ IsLocalRing.maximalIdeal O) := Ideal.Quotient.field _
  obtain ⟨i₀, i₁, hI₀, hI₁, hi₀, hi₁, hcov, hglue, hmeet⟩ :=
    Resolution.exists_twoAffineLineCover_pullback_subschemeι ((p : ℕ) : O) ((C p 𝔛 O κ toκ hϖ H).thick n)
      (Fa p O ((C p 𝔛 O κ toκ hϖ H).thick n)) (hFa p 𝔛 O hϖ κ toκ H hξ _) ((i : ℕ) + 1) (Nat.succ_pos _) hk
      (O ⧸ IsLocalRing.maximalIdeal O) (by rw [Ideal.Quotient.algebraMap_eq]; exact Ideal.Quotient.mk_surjective)
      (by rw [Ideal.Quotient.algebraMap_eq, Ideal.mk_ker, hϖ]) κ toκ
      (by rw [map_natCast, CharP.cast_eq_zero])
  haveI := hI₀; haveI := hI₁
  obtain ⟨M, eM, heM⟩ := AlgebraicCurve.CurveModel.exists_iso_of_twoAffineLineCover κ (pullback.snd _ _) i₀ i₁ hi₀ hi₁
    hcov hglue hmeet

  let lam' := AlgebraicGeometry.liftOfIsIso L.subschemeι ((C p 𝔛 O κ toκ hϖ H).g n)
  have hrange' : Set.range lam'.base = ((C p 𝔛 O κ toκ hϖ H).g n).base ⁻¹' (L.support : Set _) := by
    rw [AlgebraicGeometry.range_liftOfIsIso, Scheme.IdealSheafData.range_subschemeι]
  have hsF : lam' ≫ (C p 𝔛 O κ toκ hϖ H).toB n = L.subschemeι ≫ Resolution.toSpec ((p : ℕ) : O) ((C p 𝔛 O κ toκ hϖ H).thick n) := by
    change lam' ≫ ((C p 𝔛 O κ toκ hϖ H).g n ≫ _) = _
    rw [AlgebraicGeometry.liftOfIsIso_comp_assoc]
    rfl
  haveI := H.nodeFinite
  obtain ⟨e', he', hsnd⟩ := (C p 𝔛 O κ toκ hϖ H).exc_rational_of
    (hRF p 𝔛 O κ toκ hϖ H) (gRes p 𝔛 O κ toκ hϖ H) (hgRes p 𝔛 O κ toκ hϖ H) (ξ p 𝔛 O κ toκ) hξ n i (H.hxcl n)
    L hLsupp hcl lam' hrange' (Spec.map (CommRingCat.ofHom toκ)) _ hsF M.toBase eM heM
  exact ⟨M, e', he', hsnd⟩

end V3Asm
p2m_reactivate "P2MW.S_V3Asm_exc_rational.TwoAffineLineCover P2MW.S_V3Asm_exc_rational.AlgebraicGeometry P2MW.S_V3Asm_exc_rational.AlgebraicGeometry.Scheme P2MW.S_V3Asm_exc_rational.AlgebraicGeometry.Scheme.IdealSheafData"

end
p2m_reactivate "P2MW.S_V3Asm_exc_rational.TwoAffineLineCover P2MW.S_V3Asm_exc_rational.AlgebraicGeometry P2MW.S_V3Asm_exc_rational.AlgebraicGeometry.Scheme P2MW.S_V3Asm_exc_rational.AlgebraicGeometry.Scheme.IdealSheafData"

theorem solution (p : ℕ) [Fact p.Prime] (𝔛 : ModularCurve.DRModelPackage p)
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)})
    (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ] (toκ : O →+* κ)
    (H : V3Asm.SiteHyps p 𝔛 O κ toκ) (hξ : ∀ j, V3Asm.ξ p 𝔛 O κ toκ j ∈ (V3Asm.C p 𝔛 O κ toκ hϖ H).X0) :
    ∀ (n : V3Glue.Site.Node p 𝔛 κ) (i : Fin ((V3Asm.width p 𝔛 O κ toκ hϖ H) n - 1)),
      ∃ (M : AlgebraicCurve.CurveModel κ (RatFunc κ))
        (e : M.C ⟶ pullback ((V3Asm.comp p 𝔛 O κ toκ hϖ H hξ (Sum.inr ⟨n, i⟩)).subschemeι ≫ (V3Asm.toBase p 𝔛 O κ toκ hϖ H)) (Spec.map (CommRingCat.ofHom toκ))),
        IsIso e ∧ e ≫ pullback.snd _ _ = M.toBase :=
  V3Asm.exc_rational p 𝔛 O hϖ κ toκ H hξ

end S_V3Asm_exc_rational
end P2MW
export P2MW.S_V3Asm_exc_rational (solution)
