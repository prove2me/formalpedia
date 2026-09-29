-- Prove2me | solution 1 for WeierstrassCurve.DrinfeldGlobal.prodKerGraph_eq_ker_originChart_of_forall_reducesToOrigin
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/32865d42-9f8e-5246-9d5c-c7e01f876d70

import Mathlib
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSum
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_prodKerGraph
import Theorems.Thm_WeierstrassProjModel_projModelStrCR_isProper
import Theorems.Thm_WeierstrassProjModel_projModelStrCR_smoothOfRelativeDimension_one
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_IsOriginChartSection_map_ideal_comap_ker_eq_ker
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_map_ker_eq_span_X_sub_C_originParam
import Theorems.Thm_AlgebraicGeometry_isIso_of_isClosedImmersion_of_finrank_comp_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_DrinfeldGlobal_prodKerGraph_eq_ker_originChart_of_forall_reducesToOrigin
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero WeierstrassProjModel.quotGradingSubmoduleDegreeZeroFiniteType WeierstrassProjModel.kw_lrChart_tensorCommRing WeierstrassProjModel.kw_lrChart_biGrading_gradedAlgebra WeierstrassProjModel.projModel_isIso_spec_mapCR WeierstrassProjModel.kw_lrSymOC_isDomain_ℬ₀ WeierstrassProjModel.isProper_projModelStrCR WeierstrassProjModel.homogeneousSubmoduleDegreeZeroFiniteType"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sres AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app WeierstrassProjModel.kw_lrAdd_substHom_X WeierstrassProjModel.kw_lrSym_substHom_X"

set_option autoImplicit false

universe u

p2m_open "AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal IsLocalRing HomogeneousLocalization Polynomial AlgebraicGeometry.Polynomial"

attribute [local instance] MvPolynomial.gradedAlgebra

namespace R4SumDiv

theorem exists_basis_of_isWeierstrassFactorizationAt {A : Type*} [CommRing A] {I : Ideal A} [IsAdicComplete I A]
    {g : (PowerSeries A)} {D : A[X]} {h : (PowerSeries A)} (H : g.IsWeierstrassFactorizationAt D h I) (n : ℕ) (hn : D.natDegree = n) :
    ∃ b : Module.Basis (Fin n) A ((PowerSeries A) ⧸ Ideal.span {g}),
      ∀ i, b i = Ideal.Quotient.mk (Ideal.span {g}) (PowerSeries.X ^ (i : ℕ)) := by
  subst hn
  let pb : PowerBasis A (AdjoinRoot D) := AdjoinRoot.powerBasis' H.isDistinguishedAt.monic
  let e : (A[X] ⧸ Ideal.span {D}) ≃ₐ[A] (PowerSeries A) ⧸ Ideal.span {g} := H.algEquivQuotient
  have hdim : pb.dim = D.natDegree := rfl
  refine ⟨(pb.basis.reindex (finCongr hdim)).map e.toLinearEquiv, fun i => ?_⟩
  rw [Module.Basis.map_apply, Module.Basis.reindex_apply, pb.basis_eq_pow]
  have hgen : pb.gen = AdjoinRoot.root D := rfl
  rw [hgen]
  have hi : (((finCongr hdim).symm i : Fin pb.dim) : ℕ) = (i : ℕ) := by simp
  rw [hi]
  show e (AdjoinRoot.root D ^ (i : ℕ)) = _
  have hmk : ∀ p : A[X], e (AdjoinRoot.mk D p) = Ideal.Quotient.mk (Ideal.span {g}) (p : (PowerSeries A)) := by
    intro p
    show H.algEquivQuotient (Ideal.Quotient.mk (Ideal.span {D}) p) = _
    rw [PowerSeries.IsWeierstrassFactorizationAt.algEquivQuotient_apply, Ideal.quotient_map_mkₐ,
      Ideal.Quotient.mkₐ_eq_mk, Ideal.quotientEquivAlgOfEq_mk]
    rfl
  rw [← AdjoinRoot.mk_X, ← map_pow, hmk, Polynomial.coe_pow, Polynomial.coe_X]

noncomputable def linPoly {T : Type*} [CommRing T] {r : ℕ} (c : Fin r → T) : T[X] :=
  ∏ i, (Polynomial.X - Polynomial.C (c i))

theorem coe_linPoly {T : Type*} [CommRing T] {r : ℕ} (c : Fin r → T) :
    ((linPoly c : T[X]) : PowerSeries T) = ∏ i, (PowerSeries.X - PowerSeries.C (c i)) := by
  unfold linPoly
  rw [← Polynomial.coeToPowerSeries.ringHom_apply, map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [map_sub, Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coeToPowerSeries.ringHom_apply,
    Polynomial.coe_X, Polynomial.coe_C]

theorem monic_linPoly {T : Type*} [CommRing T] {r : ℕ} (c : Fin r → T) : (linPoly c).Monic :=
  Polynomial.monic_prod_of_monic _ _ fun _ _ => Polynomial.monic_X_sub_C _

theorem natDegree_linPoly {T : Type*} [CommRing T] [Nontrivial T] {r : ℕ} (c : Fin r → T) :
    (linPoly c).natDegree = r := by
  unfold linPoly
  rw [Polynomial.natDegree_prod_of_monic _ _ fun i _ => Polynomial.monic_X_sub_C _]
  simp

theorem isDistinguishedAt_linPoly {T : Type*} [CommRing T] (I : Ideal T) [Nontrivial T] {r : ℕ}
    (c : Fin r → T) (hc : ∀ i, c i ∈ I) : (linPoly c).IsDistinguishedAt I := by
  refine ⟨⟨fun {i} hi => ?_⟩, monic_linPoly c⟩
  rw [natDegree_linPoly] at hi
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← Polynomial.coeff_map]
  have hmap : (linPoly c).map (Ideal.Quotient.mk I) = Polynomial.X ^ r := by
    unfold linPoly
    rw [Polynomial.map_prod]
    simp_rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
      (Ideal.Quotient.eq_zero_iff_mem).mpr (hc _), map_zero, sub_zero, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
  rw [hmap, Polynomial.coeff_X_pow, if_neg (by omega)]

theorem exists_basis_quotient_prod {T : Type*} [CommRing T] [IsLocalRing T] [IsAdicComplete (maximalIdeal T) T]
    {r : ℕ} (c : Fin r → T) (hc : ∀ i, c i ∈ maximalIdeal T) :
    ∃ b : Module.Basis (Fin r) T (PowerSeries T ⧸ Ideal.span {∏ i, (PowerSeries.X - PowerSeries.C (c i))}),
      ∀ i, b i = Ideal.Quotient.mk (Ideal.span {∏ i, (PowerSeries.X - PowerSeries.C (c i))})
        (PowerSeries.X ^ (i : ℕ)) := by
  have hDist : (linPoly c).IsDistinguishedAt (maximalIdeal T) := isDistinguishedAt_linPoly _ c hc
  have hfac : (∏ i, (PowerSeries.X - PowerSeries.C (c i)) : PowerSeries T).IsWeierstrassFactorizationAt
      (linPoly c) 1 (maximalIdeal T) :=
    ⟨hDist, isUnit_one, by rw [mul_one, coe_linPoly]⟩
  exact exists_basis_of_isWeierstrassFactorizationAt hfac r (natDegree_linPoly c)

section Chart

variable {T : Type u} [CommRing T] (W : WeierstrassCurve T)

noncomputable abbrev sc : T →+* OriginChartRing W :=
  (fromZeroRingHom (projModelGradingCR W) _).comp (algebraMap T ((projModelGradingCR W) 0))

theorem originChartι_comp_projModelStrCR :
    originChartι W ≫ projModelStrCR W = Spec.map (CommRingCat.ofHom (sc W)) := by
  rw [projModelStrCR, ← Category.assoc]
  erw [Proj.awayι_toSpecZero]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

variable {W}

theorem surjective_mk_comp {g : PowerSeries T} {n : ℕ}
    (b : Module.Basis (Fin n) T (PowerSeries T ⧸ Ideal.span {g}))
    (hb : ∀ i, b i = Ideal.Quotient.mk (Ideal.span {g}) (PowerSeries.X ^ (i : ℕ)))
    (Φ : OriginChartRing W →+* PowerSeries T)
    (hΦsc : ∀ t : T, Φ (fromZeroRingHom (projModelGradingCR W) _ (algebraMap T ((projModelGradingCR W) 0) t)) =
      PowerSeries.C t)
    (hΦx : Φ (xOverY W) = - PowerSeries.X) :
    Function.Surjective ((Ideal.Quotient.mk (Ideal.span {g})).comp Φ) := by
  intro m
  set π := (Ideal.Quotient.mk (Ideal.span {g})).comp Φ with hπ
  have hπsc : ∀ t : T, π (sc W t) = algebraMap T _ t := by
    intro t
    simp only [hπ, RingHom.coe_comp, Function.comp_apply, hΦsc]
    rfl
  have hπx : π (-xOverY W) = Ideal.Quotient.mk (Ideal.span {g}) PowerSeries.X := by
    simp only [hπ, RingHom.coe_comp, Function.comp_apply, map_neg, hΦx, neg_neg]
  refine ⟨∑ i, sc W (b.repr m i) * (-xOverY W) ^ (i : ℕ), ?_⟩
  rw [map_sum]
  conv_rhs => rw [← b.sum_repr m]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, map_pow, hπsc, hπx, hb, ← map_pow]
  exact (Algebra.smul_def _ _).symm

end Chart

section Core

variable {T : Type u} [CommRing T] {W : WeierstrassCurve T}

local notation "E'" W => pullback (projModelStrCR W) (𝟙 (Spec (CommRingCat.of _)))

theorem toPullbackId_fst : (toPullbackId (W := W)) ≫ pullback.fst _ _ = 𝟙 _ :=
  pullback.lift_fst _ _ _

theorem toPullbackId_snd : (toPullbackId (W := W)) ≫ pullback.snd _ _ = projModelStrCR W :=
  pullback.lift_snd _ _ _

scoped instance isIso_toPullbackId : IsIso (toPullbackId (W := W)) := by
  have h : (toPullbackId (W := W)) ≫ pullback.fst _ _ = 𝟙 _ := toPullbackId_fst
  exact IsIso.of_isIso_fac_right h

theorem le_ker_of_map_ideal_le {M : Type u} [CommRing M] (π : OriginChartRing W →+* M)
    (𝒦 : (E' W).IdealSheafData)
    (hle : Ideal.map (Scheme.ΓSpecIso (CommRingCat.of (OriginChartRing W))).hom.hom
      ((𝒦.comap (originChartι W ≫ toPullbackId)).ideal ⟨⊤, isAffineOpen_top _⟩) ≤ RingHom.ker π) :
    𝒦 ≤ (Spec.map (CommRingCat.ofHom π) ≫ originChartι W ≫ toPullbackId).ker := by
  rw [← Scheme.IdealSheafData.map_bot, Scheme.IdealSheafData.le_map_iff_comap_le,
    Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.le_map_iff_comap_le,
    Scheme.IdealSheafData.map_bot, Scheme.ker_of_isAffine]
  refine Scheme.IdealSheafData.le_of_isAffine ?_
  rw [Scheme.IdealSheafData.ofIdealTop_ideal]
  have hid : (Spec (CommRingCat.of (OriginChartRing W))).presheaf.map
      (homOfLE (le_top (a := (⊤ : (Spec (CommRingCat.of (OriginChartRing W))).Opens)))).op = 𝟙 _ := by
    rw [show homOfLE (le_top (a := (⊤ : (Spec (CommRingCat.of (OriginChartRing W))).Opens))) = 𝟙 _ from
      Subsingleton.elim _ _]
    rw [op_id, CategoryTheory.Functor.map_id]
  intro x hx
  have hφx : ((Spec (CommRingCat.of (OriginChartRing W))).presheaf.map
      (homOfLE (le_top (a := (⊤ : (Spec (CommRingCat.of (OriginChartRing W))).Opens)))).op).hom x = x := by
    rw [hid]; rfl
  rw [← hφx]
  refine Ideal.mem_map_of_mem _ ?_

  have hnat := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom π)
  have hx' : π ((Scheme.ΓSpecIso (CommRingCat.of (OriginChartRing W))).hom.hom x) = 0 :=
    hle (Ideal.mem_map_of_mem _ hx)
  have h1 : (Scheme.ΓSpecIso (CommRingCat.of M)).hom.hom ((Spec.map (CommRingCat.ofHom π)).appTop.hom x) = 0 := by
    have := congrArg (fun f => f.hom x) hnat
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_ofHom] at this
    rw [this, hx']
  have hinj : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of M)).hom.hom :=
    (Scheme.ΓSpecIso (CommRingCat.of M)).commRingCatIsoToRingEquiv.injective
  rw [RingHom.mem_ker]
  exact hinj (by rw [h1, map_zero])

variable [IsSeparated (projModelStrCR W)]

theorem ker_eq_ker_of_rank_eq [IsNoetherianRing T]
    {M : Type u} [CommRing M] [Algebra T M] [Module.Free T M] [Module.Finite T M]
    (π : OriginChartRing W →+* M) (hπ : Function.Surjective π)
    (hπsc : ∀ t : T, π (sc W t) = algebraMap T M t)
    {n : ℕ} (hn : Module.finrank T M = n)
    {Z : Scheme.{u}} (j : Z ⟶ E' W) [IsClosedImmersion j] (g : Z ⟶ Spec (CommRingCat.of T))
    (hjg : j ≫ pullback.snd _ _ = g)
    [IsFinite g] [Flat g] [LocallyOfFinitePresentation g] (hrk : ∀ t, g.finrank t = n)
    (hle : Ideal.map (Scheme.ΓSpecIso (CommRingCat.of (OriginChartRing W))).hom.hom
      ((j.ker.comap (originChartι W ≫ toPullbackId)).ideal ⟨⊤, isAffineOpen_top _⟩) ≤ RingHom.ker π) :
    j.ker = (Spec.map (CommRingCat.ofHom π) ≫ originChartι W ≫ toPullbackId).ker := by
  set s : Spec (CommRingCat.of M) ⟶ E' W := Spec.map (CommRingCat.ofHom π) ≫ originChartι W ≫ toPullbackId
    with hs
  set mT : Spec (CommRingCat.of M) ⟶ Spec (CommRingCat.of T) :=
    Spec.map (CommRingCat.ofHom (algebraMap T M)) with hmT

  have hπsc' : π.comp (sc W) = algebraMap T M := RingHom.ext hπsc
  have hs_over : s ≫ pullback.snd _ _ = mT := by
    rw [hs, Category.assoc, Category.assoc, toPullbackId_snd, originChartι_comp_projModelStrCR,
      ← Spec.map_comp, ← CommRingCat.ofHom_comp, hπsc']

  haveI : IsFinite mT := by
    rw [hmT, IsFinite.SpecMap_iff, CommRingCat.hom_ofHom, RingHom.finite_algebraMap]; infer_instance
  haveI : Flat mT := by
    rw [hmT, Flat.SpecMap_iff, CommRingCat.hom_ofHom, RingHom.flat_algebraMap_iff]; infer_instance
  haveI : LocallyOfFinitePresentation mT := by
    rw [hmT, LocallyOfFinitePresentation.SpecMap_iff, CommRingCat.hom_ofHom,
      RingHom.finitePresentation_algebraMap]
    exact (Algebra.FinitePresentation.of_finiteType (R := T) (A := M)).mp inferInstance
  have hmT_rank : ∀ t : Spec (CommRingCat.of T), mT.finrank t = n := by
    intro t
    rw [hmT, Scheme.Hom.finrank_SpecMap_algebraMap T M t, Module.rankAtStalk_eq_finrank_of_free, hn]
    rfl

  haveI : IsClosedImmersion (Spec.map (CommRingCat.ofHom π)) :=
    IsClosedImmersion.spec_of_surjective _ (by simpa using hπ)
  haveI : IsPreimmersion s := by rw [hs]; infer_instance
  haveI : IsFinite (s ≫ pullback.snd (projModelStrCR W) (𝟙 _)) := by rw [hs_over]; infer_instance
  haveI : IsFinite s := IsFinite.of_comp s (pullback.snd (projModelStrCR W) (𝟙 _))
  haveI : IsClosedImmersion s := IsClosedImmersion.of_isPreimmersion s s.isClosedMap.isClosed_range

  have hle' : j.ker ≤ s.ker := le_ker_of_map_ideal_le π j.ker hle
  set ℓ := IsClosedImmersion.lift j s hle' with hℓ
  have hℓj : ℓ ≫ j = s := IsClosedImmersion.lift_fac j s hle'
  haveI : IsClosedImmersion (ℓ ≫ j) := by rw [hℓj]; infer_instance
  haveI : IsClosedImmersion ℓ := IsClosedImmersion.of_comp_isClosedImmersion ℓ j

  haveI : IsIso ℓ := by
    refine AlgebraicGeometry.isIso_of_isClosedImmersion_of_finrank_comp_eq ℓ g mT ?_ fun t => ?_
    · rw [← hjg, ← Category.assoc, hℓj, hs_over]
    · rw [hmT_rank, hrk]
  rw [← hℓj, Scheme.Hom.ker_comp_of_isIso]

end Core

section Graph

variable {T : Type u} [CommRing T] (W : WeierstrassCurve T)

theorem graphOver_eq (P : Section W) :
    graphOver (projModelStrCR W) P.1 P.2 = P.1 ≫ toPullbackId := by
  apply pullback.hom_ext
  · rw [graphOver_fst, Category.assoc, toPullbackId_fst, Category.comp_id]
  · rw [graphOver_snd, Category.assoc, toPullbackId_snd, P.2]

variable [IsSeparated (projModelStrCR W)]

scoped instance isClosedImmersion_section (P : Section W) : IsClosedImmersion P.1 := by
  haveI : IsClosedImmersion (P.1 ≫ projModelStrCR W) := by rw [P.2]; infer_instance
  exact IsClosedImmersion.of_comp P.1 (projModelStrCR W)

theorem comap_ker_graphOver (P : Section W) :
    (graphOver (projModelStrCR W) P.1 P.2).ker.comap (originChartι W ≫ toPullbackId) =
      (Scheme.Hom.ker P.1).comap (originChartι W) := by
  rw [Scheme.IdealSheafData.comap_comp, graphOver_eq]
  congr 1
  have hP : IsPullback P.1 (𝟙 _) (toPullbackId (W := W)) (P.1 ≫ toPullbackId) :=
    IsPullback.of_vert_isIso ⟨by rw [Category.id_comp]⟩
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion, ← hP.isoPullback_inv_fst,
    Scheme.Hom.ker_comp_of_isIso]

end Graph

section Prod

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]

theorem comap_mul (I J : Y.IdealSheafData) : (I * J).comap f = I.comap f * J.comap f := by
  apply Scheme.IdealSheafData.ext
  funext U
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion, Scheme.IdealSheafData.ideal_mul, Pi.mul_apply,
    Scheme.IdealSheafData.ideal_mul, Pi.mul_apply, Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion,
    Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion]
  set e := (f.appIso U).commRingCatIsoToRingEquiv with he
  have hcomap : ∀ K : Ideal Γ(Y, f ''ᵁ U), K.comap (f.appIso U).inv.hom = K.map e := by
    intro K
    rw [← Ideal.comap_symm]
    rfl
  rw [hcomap, hcomap, hcomap, Ideal.map_mul]

theorem comap_prod {ι : Type*} (s : Finset ι) (I : ι → Y.IdealSheafData) :
    (∏ i ∈ s, I i).comap f = ∏ i ∈ s, (I i).comap f := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.prod_insert hi, Finset.prod_insert hi, comap_mul, ih]

theorem ideal_prod {ι : Type*} (s : Finset ι) (I : ι → X.IdealSheafData) (U : X.affineOpens) :
    (∏ i ∈ s, I i).ideal U = ∏ i ∈ s, (I i).ideal U := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Ideal.one_eq_top]
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi, Scheme.IdealSheafData.ideal_mul, Pi.mul_apply, ih]

end Prod

end R4SumDiv
p2m_reactivate "P2MW.S_WeierstrassCurve_DrinfeldGlobal_prodKerGraph_eq_ker_originChart_of_forall_reducesToOrigin.R4SumDiv"

open R4SumDiv in
theorem solution
    {T : Type u} [CommRing T] [IsLocalRing T] [IsNoetherianRing T] [IsAdicComplete (maximalIdeal T) T]
    (W : WeierstrassCurve T) [W.IsElliptic]
    {r : ℕ} (R : Fin r → Section W) (χ : Fin r → (OriginChartRing W →+* T))
    (hR : ∀ i, ReducesToOrigin (R i) (χ i) (maximalIdeal T))
    (Φ : OriginChartRing W →+* PowerSeries T)
    (hΦsc : ∀ t : T, Φ (fromZeroRingHom (projModelGradingCR W) _ (algebraMap T ((projModelGradingCR W) 0) t)) =
      PowerSeries.C t)
    (hΦx : Φ (xOverY W) = - PowerSeries.X) (hΦz : Φ (zOverY W) = - W.formalW) :
    prodKerGraph (projModelStrCR W) (fun i => (R i).1) (fun i => (R i).2) =
      (Spec.map (CommRingCat.ofHom ((Ideal.Quotient.mk
          (Ideal.span {∏ i, (PowerSeries.X - PowerSeries.C (originParam (χ i)))})).comp Φ)) ≫
        originChartι W ≫ toPullbackId).ker := by

  haveI : IsProper (projModelStrCR W) := WeierstrassProjModel.projModelStrCR_isProper W
  haveI : IsSeparated (projModelStrCR W) := inferInstance
  haveI : SmoothOfRelativeDimension 1 (projModelStrCR W) :=
    WeierstrassProjModel.projModelStrCR_smoothOfRelativeDimension_one W

  obtain ⟨D, hD⟩ := AlgebraicGeometry.RelEffCartierDiv.exists_I_eq_prodKerGraph
    (f := projModelStrCR W) (fun i => (R i).1) (fun i => (R i).2)
  haveI := D.isFinite
  haveI := D.flat
  haveI := D.locallyOfFinitePresentation

  set c : Fin r → T := fun i => originParam (χ i) with hc
  set gD : PowerSeries T := ∏ i, (PowerSeries.X - PowerSeries.C (c i)) with hgD
  obtain ⟨b, hb⟩ := exists_basis_quotient_prod c fun i => (hR i).2.1
  haveI : Module.Free T (PowerSeries T ⧸ Ideal.span {gD}) := Module.Free.of_basis b
  haveI : Module.Finite T (PowerSeries T ⧸ Ideal.span {gD}) := Module.Finite.of_basis b
  have hrank : Module.finrank T (PowerSeries T ⧸ Ideal.span {gD}) = r := by
    rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
  set π := (Ideal.Quotient.mk (Ideal.span {gD})).comp Φ with hπ
  have hπsurj : Function.Surjective π := surjective_mk_comp b hb Φ hΦsc hΦx
  have hπsc : ∀ t : T, π (sc W t) = algebraMap T _ t := by
    intro t
    simp only [hπ, RingHom.coe_comp, Function.comp_apply, hΦsc]
    rfl

  have hle : Ideal.map (Scheme.ΓSpecIso (CommRingCat.of (OriginChartRing W))).hom.hom
      ((D.I.subschemeι.ker.comap (originChartι W ≫ toPullbackId)).ideal ⟨⊤, isAffineOpen_top _⟩) ≤
      RingHom.ker π := by
    rw [Scheme.IdealSheafData.ker_subschemeι, hD, prodKerGraph_eq_prod, comap_prod, ideal_prod, ← Ideal.mapHom_apply, map_prod]
    simp only [Ideal.mapHom_apply]
    have hfac : ∀ i : Fin r,
        Ideal.map (Scheme.ΓSpecIso (CommRingCat.of (OriginChartRing W))).hom.hom
          (((graphOver (projModelStrCR W) (R i).1 (R i).2).ker.comap (originChartι W ≫ toPullbackId)).ideal
            ⟨⊤, isAffineOpen_top _⟩) = RingHom.ker (χ i) := by
      intro i
      rw [comap_ker_graphOver]
      exact IsOriginChartSection.map_ideal_comap_ker_eq_ker W (R i) (χ i) (hR i).1
    simp_rw [hfac]
    intro x hx
    rw [RingHom.mem_ker, hπ, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
    have hΦx' : Φ x ∈ Ideal.map Φ (∏ i, RingHom.ker (χ i)) := Ideal.mem_map_of_mem _ hx
    rw [← Ideal.mapHom_apply, map_prod] at hΦx'
    simp only [Ideal.mapHom_apply] at hΦx'
    have himg : ∀ i : Fin r, Ideal.map Φ (RingHom.ker (χ i)) =
        Ideal.span {PowerSeries.X - PowerSeries.C (c i)} := fun i =>
      map_ker_eq_span_X_sub_C_originParam W (R i) (χ i) (hR i) Φ hΦsc hΦx hΦz
    simp_rw [himg, Ideal.prod_span_singleton] at hΦx'
    exact hΦx'

  have key := ker_eq_ker_of_rank_eq (W := W) π hπsurj hπsc hrank D.I.subschemeι
    (D.I.subschemeι ≫ pullback.snd _ _) rfl D.finrank_eq hle
  rw [Scheme.IdealSheafData.ker_subschemeι, hD] at key
  exact key

end S_WeierstrassCurve_DrinfeldGlobal_prodKerGraph_eq_ker_originChart_of_forall_reducesToOrigin
end P2MW
export P2MW.S_WeierstrassCurve_DrinfeldGlobal_prodKerGraph_eq_ker_originChart_of_forall_reducesToOrigin (solution)
