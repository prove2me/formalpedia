-- Prove2me | solution 1 for WeierstrassCurve.DrinfeldGlobal.isFinite_pullback_snd_kwZeroSect_flat_finrank_eq_of_zChart_pow_originChart_pow_of_ringEquiv_adjoinRoot
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/52d75c5a-6170-54e8-a8cf-9beea1868c7b

import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_PointChart
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Theorems.Thm_WeierstrassProjModel_isOriginChartSection_kwZeroSect_kwYChartEval
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_ker_eq_span_of_originChartRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_DrinfeldGlobal_isFinite_pullback_snd_kwZeroSect_flat_finrank_eq_of_zChart_pow_originChart_pow_of_ringEquiv_adjoinRoot

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal HomogeneousLocalization

attribute [local instance] MvPolynomial.gradedAlgebra

namespace DGeo

section Affine

variable {T : Type} [CommRing T] [Nontrivial T] {Q : Type} [CommRing Q] (σ : T →+* Q) (q : ℕ)

theorem affine_tail (e : Q ≃+* AdjoinRoot ((Polynomial.X : Polynomial T) ^ q))
    (he : ∀ t : T, e (σ t) = algebraMap T (AdjoinRoot ((Polynomial.X : Polynomial T) ^ q)) t) :
    IsFinite (Spec.map (CommRingCat.ofHom σ)) ∧ Flat (Spec.map (CommRingCat.ofHom σ)) ∧
      LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom σ)) ∧
      ∀ s, (Spec.map (CommRingCat.ofHom σ)).finrank s = q := by
  letI : Algebra T Q := σ.toAlgebra
  have hmonic : ((Polynomial.X : Polynomial T) ^ q).Monic := Polynomial.monic_X_pow q
  let e' : Q ≃ₐ[T] AdjoinRoot ((Polynomial.X : Polynomial T) ^ q) := AlgEquiv.ofRingEquiv (f := e) he
  haveI : Module.Free T (AdjoinRoot ((Polynomial.X : Polynomial T) ^ q)) := hmonic.free_adjoinRoot
  haveI : Module.Finite T (AdjoinRoot ((Polynomial.X : Polynomial T) ^ q)) := hmonic.finite_adjoinRoot
  haveI hfree : Module.Free T Q := Module.Free.of_equiv e'.symm.toLinearEquiv
  haveI hfin : Module.Finite T Q := Module.Finite.equiv e'.symm.toLinearEquiv
  haveI hfp : Algebra.FinitePresentation T Q := Algebra.FinitePresentation.equiv e'.symm
  have hrank : Module.finrank T Q = q := by
    rw [e'.toLinearEquiv.finrank_eq, (AdjoinRoot.powerBasis' hmonic).finrank]
    simp [AdjoinRoot.powerBasis']
  have hσ : σ = algebraMap T Q := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [IsFinite.SpecMap_iff]; exact RingHom.finite_algebraMap.mpr hfin
  · rw [Flat.SpecMap_iff]; exact (RingHom.flat_algebraMap_iff).mpr inferInstance
  · rw [LocallyOfFinitePresentation.SpecMap_iff]; exact (RingHom.finitePresentation_algebraMap).mpr hfp
  · intro s
    rw [hσ, Scheme.Hom.finrank_SpecMap_algebraMap, Module.rankAtStalk_eq_finrank_of_free, hrank]
    rfl

end Affine

section Pushout

variable {A' A T : Type} [CommRing A'] [CommRing A] [CommRing T]

theorem isPushout_quotient (ψ : A' →+* A) (χ : A' →+* T) (c' : T →+* A') (c : T →+* A)
    (hχc' : ∀ t, χ (c' t) = t) (hψc' : ∀ t, ψ (c' t) = c t) (I : Ideal A)
    (hI : Ideal.map ψ (RingHom.ker χ) = I) :
    IsPushout (CommRingCat.ofHom ψ) (CommRingCat.ofHom χ) (CommRingCat.ofHom (Ideal.Quotient.mk I))
      (CommRingCat.ofHom ((Ideal.Quotient.mk I).comp c)) := by

  have hcomm : ∀ a : A', Ideal.Quotient.mk I (ψ a) = Ideal.Quotient.mk I (c (χ a)) := by
    intro a
    rw [Ideal.Quotient.eq, ← hI, ← hψc', ← map_sub]
    exact Ideal.mem_map_of_mem _ (by rw [RingHom.mem_ker, map_sub, hχc', sub_self])
  have w : CommSq (CommRingCat.ofHom ψ) (CommRingCat.ofHom χ) (CommRingCat.ofHom (Ideal.Quotient.mk I))
      (CommRingCat.ofHom ((Ideal.Quotient.mk I).comp c)) :=
    ⟨by ext a; simpa using hcomm a⟩
  refine IsPushout.of_isColimit' w (PushoutCocone.IsColimit.mk _ (fun s => ?_) (fun s => ?_) (fun s => ?_) ?_)
  ·
    have hker : I ≤ RingHom.ker s.inl.hom := by
      rw [← hI, Ideal.map_le_iff_le_comap]
      intro a' ha'
      rw [Ideal.mem_comap, RingHom.mem_ker]
      have := CategoryTheory.congr_fun s.condition a'
      simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_ofHom] at this
      rw [this, (RingHom.mem_ker).mp ha', map_zero]
    exact CommRingCat.ofHom (Ideal.Quotient.lift I s.inl.hom fun a ha => hker ha)
  · ext a; rfl
  · ext t
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_ofHom,
      Ideal.Quotient.lift_mk]
    have := CategoryTheory.congr_fun s.condition (c' t)
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_ofHom, hχc',
      hψc'] at this
    exact this
  · intro s m hm₁ hm₂
    ext a
    have := CategoryTheory.congr_fun hm₁ a
    simpa using this

end Pushout

section Extend

theorem isPullback_comp_of_isOpenImmersion {P X₀ X S Y₀ Y : Scheme} {a : P ⟶ X₀} {b : P ⟶ S} {f₀ : X₀ ⟶ Y₀}
    {g₀ : S ⟶ Y₀} (h₀ : IsPullback a b f₀ g₀) (ι : X₀ ⟶ X) (ι' : Y₀ ⟶ Y) [IsOpenImmersion ι] [Mono ι']
    (Φ : X ⟶ Y) (hsq : ι ≫ Φ = f₀ ≫ ι')
    (hcover : ∀ x : X, Φ x ∈ Set.range (g₀ ≫ ι') → x ∈ Set.range ι) :
    IsPullback (a ≫ ι) b Φ (g₀ ≫ ι') := by
  have wcomm : (a ≫ ι) ≫ Φ = b ≫ g₀ ≫ ι' := by
    rw [Category.assoc, hsq, ← Category.assoc, h₀.w, Category.assoc]
  refine IsPullback.of_isLimit' ⟨wcomm⟩ (PullbackCone.IsLimit.mk wcomm (fun s => ?_) (fun s => ?_) (fun s => ?_) ?_)
  ·
    have hrange : Set.range s.fst ⊆ Set.range ι := by
      rintro _ ⟨p, rfl⟩
      apply hcover
      refine ⟨s.snd p, ?_⟩
      rw [← Scheme.Hom.comp_apply, ← s.condition, Scheme.Hom.comp_apply]
    have hfac := IsOpenImmersion.lift_fac ι s.fst hrange
    refine h₀.lift (IsOpenImmersion.lift ι s.fst hrange) s.snd ?_
    rw [← cancel_mono ι', Category.assoc, ← hsq, ← Category.assoc, hfac, s.condition, Category.assoc]
  · simp only
    rw [← Category.assoc, IsPullback.lift_fst, IsOpenImmersion.lift_fac]
  · simp only
    rw [IsPullback.lift_snd]
  · intro s m hm₁ hm₂
    apply h₀.hom_ext
    · rw [← cancel_mono ι, Category.assoc, hm₁, IsPullback.lift_fst, IsOpenImmersion.lift_fac]
    · rw [hm₂, IsPullback.lift_snd]

end Extend

section Cover

open MvPolynomial TopologicalSpace

variable {R : Type} [CommRing R] (V : WeierstrassCurve.Projective R)

theorem polynomial_add_X0_cube :
    V.polynomial + X 0 ^ 3 = X 2 * (X 1 ^ 2 + C V.a₁ * X 0 * X 1 + C V.a₃ * X 1 * X 2
      - C V.a₂ * X 0 ^ 2 - C V.a₄ * X 0 * X 2 - C V.a₆ * X 2 ^ 2) := by
  rw [WeierstrassCurve.Projective.polynomial]
  ring

theorem not_mem_and_mem (x : Proj (projModelGradingCR V)) :
    ¬ (coord V 1 ∈ x.asHomogeneousIdeal ∧ coord V 2 ∈ x.asHomogeneousIdeal) := by
  rintro ⟨h1, h2⟩
  have hpoly : Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal V.polynomial = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  have hid := congrArg (Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal) (polynomial_add_X0_cube V)
  rw [map_add, map_mul, map_pow, hpoly, zero_add] at hid
  have h0 : coord V 0 ∈ x.asHomogeneousIdeal.toIdeal := by
    apply x.isPrime.mem_of_pow_mem 3
    change Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal (X 0 : MvPolynomial (Fin 3) R) ^ 3 ∈ _
    rw [hid]
    exact Ideal.mul_mem_right _ _ h2
  have hspan : Ideal.span (Set.range fun i : Fin 3 ↦
      Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal (X i : MvPolynomial (Fin 3) R))
        ≤ x.asHomogeneousIdeal.toIdeal := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
  exact x.not_irrelevant_le fun z hz ↦ hspan (kw_pbac_irrelevant_le_span_mk_X_CR R V hz)

theorem mem_basicOpen_or (x : Proj (projModelGradingCR V)) :
    x ∈ Proj.basicOpen (projModelGradingCR V) (coord V 1) ∨ x ∈ Proj.basicOpen (projModelGradingCR V) (coord V 2) := by
  rw [Proj.mem_basicOpen, Proj.mem_basicOpen]
  by_cases h1 : coord V 1 ∈ x.asHomogeneousIdeal
  · exact Or.inr fun h2 => not_mem_and_mem V x ⟨h1, h2⟩
  · exact Or.inl h1

theorem isLocalizationElem_eq_zOverY :
    Away.isLocalizationElem (coord_mem V 1) (coord_mem V 2) = zOverY V := by
  apply HomogeneousLocalization.val_injective
  simp [Away.isLocalizationElem, zOverY, Away.mk, HomogeneousLocalization.val_mk, pow_one]

end Cover

theorem cover (q : ℕ) [Fact q.Prime] (T : Type) [CommRing T] [CharP T q] (W : WeierstrassCurve T)
    (Φ : projModelCR W.toProjective ⟶ projModelCR (W.map (frobenius T q)).toProjective)
    (hZ : ∃ ψ : ZChartRing (W.map (frobenius T q)).toProjective →+* ZChartRing W.toProjective,
        ψ (xOverZ (W.map (frobenius T q)).toProjective) = xOverZ W.toProjective ^ q ∧
        ψ (yOverZ (W.map (frobenius T q)).toProjective) = yOverZ W.toProjective ^ q ∧
        zChartι W.toProjective ≫ Φ = Spec.map (CommRingCat.ofHom ψ) ≫ zChartι (W.map (frobenius T q)).toProjective)
    (x : ↥(projModelCR W.toProjective))
    (hx : Φ x ∈ Set.range (kwZeroSect T (W.map (frobenius T q))).1) :
    x ∈ Set.range (originChartι W.toProjective) := by
  let V : WeierstrassCurve.Projective T := W.toProjective
  let V' : WeierstrassCurve.Projective T := (W.map (frobenius T q)).toProjective
  obtain ⟨ψZ, -, -, hcommZ⟩ := hZ
  obtain ⟨t, ht⟩ := hx
  obtain ⟨hO, -, hχz⟩ :=
    WeierstrassProjModel.isOriginChartSection_kwZeroSect_kwYChartEval (W.map (frobenius T q)).toProjective
  rcases mem_basicOpen_or V x with hY | hZ2
  ·
    have : x ∈ (originChartι V).opensRange := by rw [Proj.opensRange_awayι]; exact hY
    exact this
  ·
    exfalso
    have hx2 : x ∈ (zChartι V).opensRange := by rw [Proj.opensRange_awayι]; exact hZ2
    obtain ⟨y, rfl⟩ := hx2
    have hmem : Φ (zChartι V y) ∈ Proj.basicOpen (projModelGradingCR V') (coord V' 2) := by
      rw [← Scheme.Hom.comp_apply, hcommZ, Scheme.Hom.comp_apply]
      have : zChartι V' (Spec.map (CommRingCat.ofHom ψZ) y) ∈ (zChartι V').opensRange := ⟨_, rfl⟩
      rwa [Proj.opensRange_awayι] at this
    rw [← ht] at hmem
    have hO' : (kwZeroSect T (W.map (frobenius T q))).1 =
        Spec.map (CommRingCat.ofHom (kwYChartEval T (W.map (frobenius T q)))) ≫ originChartι V' := hO
    rw [hO', Scheme.Hom.comp_apply] at hmem
    have hpre : Spec.map (CommRingCat.ofHom (kwYChartEval T (W.map (frobenius T q)))) t ∈
        originChartι V' ⁻¹ᵁ Proj.basicOpen (projModelGradingCR V') (coord V' 2) := hmem
    rw [Proj.awayι_preimage_basicOpen (projModelGradingCR V') (coord_mem V' 1) one_pos (coord_mem V' 2) one_pos,
      isLocalizationElem_eq_zOverY] at hpre
    refine (PrimeSpectrum.mem_basicOpen _ _).mp hpre ?_
    change kwYChartEval T (W.map (frobenius T q)) (zOverY V') ∈ t.asIdeal
    rw [hχz]
    exact Ideal.zero_mem _

theorem main (q : ℕ) [Fact q.Prime] (T : Type) [CommRing T] [CharP T q] (W : WeierstrassCurve T)
    (Φ : projModelCR W.toProjective ⟶ projModelCR (W.map (frobenius T q)).toProjective)
    (hΦ : Φ ≫ projModelStrCR (W.map (frobenius T q)).toProjective = projModelStrCR W.toProjective)
    (hZ : ∃ ψ : ZChartRing (W.map (frobenius T q)).toProjective →+* ZChartRing W.toProjective,
        ψ (xOverZ (W.map (frobenius T q)).toProjective) = xOverZ W.toProjective ^ q ∧
        ψ (yOverZ (W.map (frobenius T q)).toProjective) = yOverZ W.toProjective ^ q ∧
        zChartι W.toProjective ≫ Φ = Spec.map (CommRingCat.ofHom ψ) ≫ zChartι (W.map (frobenius T q)).toProjective)
    (hY : ∃ ψ : OriginChartRing (W.map (frobenius T q)).toProjective →+* OriginChartRing W.toProjective,
        ψ (xOverY (W.map (frobenius T q)).toProjective) = xOverY W.toProjective ^ q ∧
        ψ (zOverY (W.map (frobenius T q)).toProjective) = zOverY W.toProjective ^ q ∧
        originChartι W.toProjective ≫ Φ = Spec.map (CommRingCat.ofHom ψ) ≫ originChartι (W.map (frobenius T q)).toProjective)
    (halg : ∃ e : (OriginChartRing W.toProjective ⧸
          Ideal.span {xOverY W.toProjective ^ q, zOverY W.toProjective ^ q}) ≃+* AdjoinRoot ((Polynomial.X : Polynomial T) ^ q),
      (∀ t : T, e (Ideal.Quotient.mk _ (HomogeneousLocalization.fromZeroRingHom (projModelGradingCR W.toProjective) _ (algebraMap T ((projModelGradingCR W.toProjective) 0) t))) =
        algebraMap T (AdjoinRoot ((Polynomial.X : Polynomial T) ^ q)) t) ∧
      e (Ideal.Quotient.mk _ (xOverY W.toProjective)) = AdjoinRoot.root ((Polynomial.X : Polynomial T) ^ q)) :
    IsFinite (pullback.snd Φ (kwZeroSect T (W.map (frobenius T q))).1) ∧ Flat (pullback.snd Φ (kwZeroSect T (W.map (frobenius T q))).1) ∧
      LocallyOfFinitePresentation (pullback.snd Φ (kwZeroSect T (W.map (frobenius T q))).1) ∧
      ∀ s, (pullback.snd Φ (kwZeroSect T (W.map (frobenius T q))).1).finrank s = q := by
  have hq : q.Prime := Fact.out
  haveI : Nontrivial T := CharP.nontrivial_of_char_ne_one hq.one_lt.ne'
  obtain ⟨ψ, hψx, hψz, hcomm⟩ := hY
  obtain ⟨e, he1, he2⟩ := halg
  obtain ⟨hO, hχx, hχz⟩ :=
    WeierstrassProjModel.isOriginChartSection_kwZeroSect_kwYChartEval (W.map (frobenius T q)).toProjective

  let V : WeierstrassCurve.Projective T := W.toProjective
  let V' : WeierstrassCurve.Projective T := (W.map (frobenius T q)).toProjective
  let χ₀ := kwYChartEval T (W.map (frobenius T q))
  let c : T →+* OriginChartRing V :=
    (fromZeroRingHom (projModelGradingCR V) _).comp (algebraMap T ((projModelGradingCR V) 0))
  let c' : T →+* OriginChartRing V' :=
    (fromZeroRingHom (projModelGradingCR V') _).comp (algebraMap T ((projModelGradingCR V') 0))
  let I : Ideal (OriginChartRing V) := Ideal.span {xOverY V ^ q, zOverY V ^ q}
  let σ : T →+* OriginChartRing V ⧸ I := (Ideal.Quotient.mk I).comp c

  have hχc' : ∀ t, χ₀ (c' t) = t := fun t =>
    RingHom.congr_fun (kwYChartEval_section T (W.map (frobenius T q))) t

  have hstr : ∀ (U : WeierstrassCurve.Projective T),
      originChartι U ≫ projModelStrCR U =
        Spec.map (CommRingCat.ofHom ((fromZeroRingHom (projModelGradingCR U) _).comp
          (algebraMap T ((projModelGradingCR U) 0)))) := by
    intro U
    simp only [projModelStrCR]
    rw [← Category.assoc, Proj.awayι_toSpecZero, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have hψc' : ∀ t, ψ (c' t) = c t := by
    have h2 : Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (CommRingCat.ofHom c') = Spec.map (CommRingCat.ofHom c) := by
      rw [← hstr V', ← Category.assoc, ← hcomm, Category.assoc, hΦ, hstr V]
    have h3 : CommRingCat.ofHom c' ≫ CommRingCat.ofHom ψ = CommRingCat.ofHom c :=
      Spec.map_injective (by rw [Spec.map_comp]; exact h2)
    intro t
    have := congrArg (fun f : CommRingCat.of T ⟶ CommRingCat.of (OriginChartRing V) => f.hom t) h3
    simpa using this

  have hker : RingHom.ker χ₀ = Ideal.span {xOverY V', zOverY V'} := by
    have := WeierstrassCurve.DrinfeldGlobal.ker_eq_span_of_originChartRing (W.map (frobenius T q)) χ₀ hχc'
    rw [this, hχx, hχz, map_zero, map_zero, sub_zero, sub_zero]
  have hI : Ideal.map ψ (RingHom.ker χ₀) = I := by
    rw [hker, Ideal.map_span, Set.image_insert_eq, Set.image_singleton, hψx, hψz]

  have hpo := isPushout_quotient ψ χ₀ c' c hχc' hψc' I hI
  have hsq0 := isPullback_SpecMap_of_isPushout _ _ _ _ hpo

  have hsqE : IsPullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ originChartι V)
      (Spec.map (CommRingCat.ofHom σ)) Φ (Spec.map (CommRingCat.ofHom χ₀) ≫ originChartι V') := by
    refine isPullback_comp_of_isOpenImmersion hsq0 (originChartι V) (originChartι V') Φ hcomm ?_
    intro x hxr
    refine cover q T W Φ hZ x ?_
    rw [hO]
    exact hxr
  rw [← hO] at hsqE

  have key : pullback.snd Φ (kwZeroSect T (W.map (frobenius T q))).1 =
      hsqE.isoPullback.inv ≫ Spec.map (CommRingCat.ofHom σ) :=
    (Iso.eq_inv_comp _).mpr hsqE.isoPullback_hom_snd
  obtain ⟨h1, h2, h3, h4⟩ := affine_tail σ q e he1
  rw [key]
  refine ⟨inferInstance, inferInstance, inferInstance, fun s => ?_⟩
  rw [Scheme.Hom.finrank_comp_left_of_isIso]
  exact h4 s

end DGeo

open CategoryTheory.Limits in

theorem solution
    (q : ℕ) [Fact q.Prime] (T : Type) [CommRing T] [CharP T q] (W : WeierstrassCurve T)
    (Φ : projModelCR W.toProjective ⟶ projModelCR (W.map (frobenius T q)).toProjective)
    (hΦ : Φ ≫ projModelStrCR (W.map (frobenius T q)).toProjective = projModelStrCR W.toProjective)
    (hZ : ∃ ψ : ZChartRing (W.map (frobenius T q)).toProjective →+* ZChartRing W.toProjective,
        ψ (xOverZ (W.map (frobenius T q)).toProjective) = xOverZ W.toProjective ^ q ∧
        ψ (yOverZ (W.map (frobenius T q)).toProjective) = yOverZ W.toProjective ^ q ∧
        zChartι W.toProjective ≫ Φ = Spec.map (CommRingCat.ofHom ψ) ≫ zChartι (W.map (frobenius T q)).toProjective)
    (hY : ∃ ψ : OriginChartRing (W.map (frobenius T q)).toProjective →+* OriginChartRing W.toProjective,
        ψ (xOverY (W.map (frobenius T q)).toProjective) = xOverY W.toProjective ^ q ∧
        ψ (zOverY (W.map (frobenius T q)).toProjective) = zOverY W.toProjective ^ q ∧
        originChartι W.toProjective ≫ Φ = Spec.map (CommRingCat.ofHom ψ) ≫ originChartι (W.map (frobenius T q)).toProjective)
    (halg : ∃ e : (OriginChartRing W.toProjective ⧸
          Ideal.span {xOverY W.toProjective ^ q, zOverY W.toProjective ^ q}) ≃+* AdjoinRoot ((Polynomial.X : Polynomial T) ^ q),
      (∀ t : T, e (Ideal.Quotient.mk _ (HomogeneousLocalization.fromZeroRingHom (projModelGradingCR W.toProjective) _ (algebraMap T ((projModelGradingCR W.toProjective) 0) t))) =
        algebraMap T (AdjoinRoot ((Polynomial.X : Polynomial T) ^ q)) t) ∧
      e (Ideal.Quotient.mk _ (xOverY W.toProjective)) = AdjoinRoot.root ((Polynomial.X : Polynomial T) ^ q)) :
    IsFinite (pullback.snd Φ (kwZeroSect T (W.map (frobenius T q))).1) ∧ Flat (pullback.snd Φ (kwZeroSect T (W.map (frobenius T q))).1) ∧
      LocallyOfFinitePresentation (pullback.snd Φ (kwZeroSect T (W.map (frobenius T q))).1) ∧
      ∀ s, (pullback.snd Φ (kwZeroSect T (W.map (frobenius T q))).1).finrank s = q :=
  DGeo.main q T W Φ hΦ hZ hY halg

end S_WeierstrassCurve_DrinfeldGlobal_isFinite_pullback_snd_kwZeroSect_flat_finrank_eq_of_zChart_pow_originChart_pow_of_ringEquiv_adjoinRoot
end P2MW
export P2MW.S_WeierstrassCurve_DrinfeldGlobal_isFinite_pullback_snd_kwZeroSect_flat_finrank_eq_of_zChart_pow_originChart_pow_of_ringEquiv_adjoinRoot (solution)
