-- Prove2me | solution 1 for WeierstrassCurve.DrinfeldGlobal.torsionIdeal_comap_fst_eq_torsionIdeal_comap_theta
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/3045fcdb-4681-5386-84ac-e40adf64a24a

import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_GroupLaws_mul_comp_projMap_eq_at_field_of_isCoefficientHom
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_GroupLaws_one_comp_projMap_eq_of_isCoefficientHom
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_projMap_comp_projModelStrCR_of_isCoefficientHom
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_isPullback_projMap_of_isCoefficientHom
import Theorems.Thm_WeierstrassProjModel_projModelStrCR_isProper
import Theorems.Thm_WeierstrassProjModel_isProper_and_isIntegral_and_isReduced_selfPullback_pullback_snd_of_baseChangeIso
import Theorems.Thm_WeierstrassProjModel_projModel_pullback_iso_baseChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_DrinfeldGlobal_torsionIdeal_comap_fst_eq_torsionIdeal_comap_theta
p2m_attr_erase "instance" "WeierstrassProjModel.quotGradingSubmoduleDegreeZeroFiniteType WeierstrassProjModel.kw_lrChart_tensorCommRing WeierstrassProjModel.kw_lrChart_biGrading_gradedAlgebra WeierstrassProjModel.projModel_isIso_spec_mapCR WeierstrassProjModel.kw_lrSymOC_isDomain_ℬ₀ WeierstrassProjModel.isProper_projModelStrCR WeierstrassProjModel.homogeneousSubmoduleDegreeZeroFiniteType"
p2m_attr_erase "simp" "WeierstrassProjModel.kw_lrAdd_substHom_X WeierstrassProjModel.kw_lrSym_substHom_X GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left"

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal NeronModelInfra

namespace P3TorsionComap

theorem ker_fst_comp_eq_comap {X Y Z W : Scheme.{u}} (m : X ⟶ Y) (i : Z ⟶ Y) [IsClosedImmersion i]
    (u : X ⟶ W) (v : W ⟶ X) [IsIso v] (hvu : v ≫ u = 𝟙 W) :
    (pullback.fst m i ≫ u).ker = i.ker.comap (v ≫ m) := by
  rw [Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion i m,
    ← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion (pullback.fst m i) v]
  have h : pullback.fst v (pullback.fst m i) =
      pullback.snd v (pullback.fst m i) ≫ (pullback.fst m i ≫ u) := by
    rw [← Category.assoc, ← pullback.condition, Category.assoc, hvu, Category.comp_id]
  rw [h]
  exact (Scheme.Hom.ker_comp_of_isIso (pullback.snd v (pullback.fst m i)) _).symm

theorem isClosedImmersion_of_comp_eq_id {S E : Scheme.{u}} (e : S ⟶ E) (p : E ⟶ S) [IsSeparated p]
    (h : e ≫ p = 𝟙 S) : IsClosedImmersion e := by
  have : IsClosedImmersion (e ≫ p) := by rw [h]; infer_instance
  exact IsClosedImmersion.of_comp e p

theorem ker_eq_comap_of_isPullback {S S' E E' : Scheme.{u}} (e : S ⟶ E) (p : E ⟶ S) (e' : S' ⟶ E')
    (p' : E' ⟶ S') (g : E' ⟶ E) (b : S' ⟶ S) [IsSeparated p]
    (he : e ≫ p = 𝟙 S) (he' : e' ≫ p' = 𝟙 S') (hsq : IsPullback g p' p b) (hcomm : e' ≫ g = b ≫ e) :
    e'.ker = e.ker.comap g := by
  haveI : IsClosedImmersion e := isClosedImmersion_of_comp_eq_id e p he
  have s : IsPullback (e' ≫ p') b b (e ≫ p) := by
    rw [he, he']
    exact IsPullback.of_id_fst
  have hP : IsPullback e' b g e := IsPullback.of_right s hcomm hsq.flip
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion e g, ← hP.isoPullback_hom_fst,
    Scheme.Hom.ker_comp_of_isIso]

theorem isReduced_projModelCR {K : Type u} [Field K] (V : WeierstrassCurve.Projective K)
    (hΔ : IsUnit V.Δ) : IsReduced (projModelCR V) := by
  haveI : V.toAffine.IsElliptic := ⟨hΔ⟩
  obtain ⟨-, hint, -⟩ :=
    WeierstrassProjModel.isProper_and_isIntegral_and_isReduced_selfPullback_pullback_snd_of_baseChangeIso V K
      (WeierstrassProjModel.projModel_pullback_iso_baseChange V K)
  haveI := hint
  haveI : IsIso (Spec.map (CommRingCat.ofHom (algebraMap K K))) := by
    show IsIso (Spec.map (𝟙 _))
    infer_instance
  exact isReduced_of_isOpenImmersion
    (inv (pullback.fst (projModelStrCR V) (Spec.map (CommRingCat.ofHom (algebraMap K K)))))

theorem schemeNsmul_comp_eq_comp_schemeNsmul
    {T K : Type u} [CommRing T] [Field K] (W : WeierstrassCurve T) (f : T →+* K)
    (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (W.map f))
    (hφ : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map f)) ≤
      (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ)
    (hsq : Proj.map φ hφ ≫ projModelStrCR W = projModelStrCR (W.map f) ≫ Spec.map (CommRingCat.ofHom f))
    (G : RelativeGroupLaw T (projModelStrCR W)) (L : RelativeGroupLaw K (projModelStrCR (W.map f)))
    [IsSeparated (projModelStrCR W)] [IsReduced (projModelCR (W.map f))]
    (h1 : ∀ {S : Scheme.{u}} (s : S ⟶ Spec (CommRingCat.of K)),
      (L.one s).1 ≫ Proj.map φ hφ = (G.one (s ≫ Spec.map (CommRingCat.ofHom f))).1)
    (hmul : ∀ (F : Type u) [Field F] [Algebra K F]
      (x y : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K F))) (projModelStrCR (W.map f)))
      (x' y' : SchemeHomOver
        (Spec.map (CommRingCat.ofHom (algebraMap K F)) ≫ Spec.map (CommRingCat.ofHom f)) (projModelStrCR W)),
      x'.1 = x.1 ≫ Proj.map φ hφ → y'.1 = y.1 ≫ Proj.map φ hφ →
        (L.mul (Spec.map (CommRingCat.ofHom (algebraMap K F))) x y).1 ≫ Proj.map φ hφ =
          (G.mul (Spec.map (CommRingCat.ofHom (algebraMap K F)) ≫ Spec.map (CommRingCat.ofHom f)) x' y').1)
    (n : ℕ) :
    L.schemeNsmul n ≫ Proj.map φ hφ = Proj.map φ hφ ≫ G.schemeNsmul n := by
  apply ext_of_fromSpecResidueField_eq _ _ (projModelStrCR W) Set.univ dense_univ
  · intro x _

    let X : Scheme.{u} := projModelCR (W.map f)
    let F : Type u := ↑(X.residueField x)
    let zx : Spec (CommRingCat.of F) ⟶ X := X.fromSpecResidueField x
    letI alg : Algebra K F := (Spec.preimage (zx ≫ projModelStrCR (W.map f))).hom.toAlgebra
    have hs : Spec.map (CommRingCat.ofHom (algebraMap K F)) = zx ≫ projModelStrCR (W.map f) := by
      show Spec.map (Spec.preimage (zx ≫ projModelStrCR (W.map f))) = _
      exact Spec.map_preimage _
    have hs' : (zx ≫ Proj.map φ hφ) ≫ projModelStrCR W =
        Spec.map (CommRingCat.ofHom (algebraMap K F)) ≫ Spec.map (CommRingCat.ofHom f) := by
      rw [Category.assoc, hsq, ← Category.assoc, hs]
    let xPt : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K F))) (projModelStrCR (W.map f)) :=
      ⟨zx, hs.symm⟩
    let xPt' : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K F)) ≫ Spec.map (CommRingCat.ofHom f))
        (projModelStrCR W) :=
      ⟨zx ≫ Proj.map φ hφ, hs'⟩

    have key : ∀ m : ℕ, (L.nsmul (Spec.map (CommRingCat.ofHom (algebraMap K F))) m xPt).1 ≫ Proj.map φ hφ =
        (G.nsmul (Spec.map (CommRingCat.ofHom (algebraMap K F)) ≫ Spec.map (CommRingCat.ofHom f)) m xPt').1 := by
      intro m
      induction m with
      | zero => exact h1 _
      | succ m ih =>
          rw [RelativeGroupLaw.nsmul_succ, RelativeGroupLaw.nsmul_succ]
          exact hmul F _ xPt _ xPt' ih.symm rfl

    have hL : zx ≫ L.schemeNsmul n = (L.nsmul (Spec.map (CommRingCat.ofHom (algebraMap K F))) n xPt).1 := by
      have hid : schemeHomOverComp zx hs.symm (RelativeGroupLaw.idPoint) = xPt :=
        Subtype.ext (Category.comp_id _)
      have := congrArg Subtype.val
        (L.nsmul_natural (projModelStrCR (W.map f)) _ zx hs.symm n RelativeGroupLaw.idPoint)
      rw [hid] at this
      exact this
    have hG : (zx ≫ Proj.map φ hφ) ≫ G.schemeNsmul n =
        (G.nsmul (Spec.map (CommRingCat.ofHom (algebraMap K F)) ≫ Spec.map (CommRingCat.ofHom f)) n xPt').1 := by
      have hid : schemeHomOverComp (zx ≫ Proj.map φ hφ) hs' (RelativeGroupLaw.idPoint) = xPt' :=
        Subtype.ext (Category.comp_id _)
      have := congrArg Subtype.val
        (G.nsmul_natural (projModelStrCR W) _ (zx ≫ Proj.map φ hφ) hs' n RelativeGroupLaw.idPoint)
      rw [hid] at this
      exact this
    show zx ≫ (L.schemeNsmul n ≫ Proj.map φ hφ) = zx ≫ (Proj.map φ hφ ≫ G.schemeNsmul n)
    rw [← Category.assoc, hL, key, ← hG, Category.assoc]
  · rw [Category.assoc, Category.assoc, G.schemeNsmul_over, hsq, ← Category.assoc, L.schemeNsmul_over]

end P3TorsionComap

open P3TorsionComap in

theorem solution
    (A : Type u) [CommRing A] (𝒢 : GroupLaws A) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)
    (T : Type u) [CommRing T] [Algebra A T] (K : Type u) [Field K] [Algebra A K] (ι : T →ₐ[A] K)
    (W₀ : WeierstrassCurve T) (hΔ₀ : IsUnit W₀.Δ) (hΔ' : IsUnit (W₀.map ι.toRingHom).Δ) (n : ℕ)
    (φ : projModelGradingCR W₀ →+*ᵍ projModelGradingCR (W₀.map ι.toRingHom))
    (hφ : HomogeneousIdeal.irrelevant (projModelGradingCR (W₀.map ι.toRingHom)) ≤
      (HomogeneousIdeal.irrelevant (projModelGradingCR W₀)).map φ)
    (hφc : IsCoefficientHom W₀ ι.toRingHom φ)
    (θ : pullback (pullback.snd (projModelStrCR W₀) (𝟙 (Spec (CommRingCat.of T))))
          (Spec.map (CommRingCat.ofHom ι.toRingHom)) ⟶
        pullback (projModelStrCR (W₀.map ι.toRingHom)) (𝟙 (Spec (CommRingCat.of K))))
    (hθ₁ : θ ≫ pullback.fst _ _ ≫ Proj.map φ hφ =
      pullback.fst (pullback.snd (projModelStrCR W₀) (𝟙 _)) (Spec.map (CommRingCat.ofHom ι.toRingHom)) ≫
        pullback.fst _ _)
    (hθ₂ : θ ≫ pullback.snd _ _ =
      pullback.snd (pullback.snd (projModelStrCR W₀) (𝟙 _)) (Spec.map (CommRingCat.ofHom ι.toRingHom))) :
    (torsionIdeal (𝒢 T W₀ hΔ₀) n).comap
        (pullback.fst (pullback.snd (projModelStrCR W₀) (𝟙 _)) (Spec.map (CommRingCat.ofHom ι.toRingHom))) =
      (torsionIdeal (𝒢 K (W₀.map ι.toRingHom) hΔ') n).comap θ := by

  have hsq : Proj.map φ hφ ≫ projModelStrCR W₀ =
      projModelStrCR (W₀.map ι.toRingHom) ≫ Spec.map (CommRingCat.ofHom ι.toRingHom) :=
    projMap_comp_projModelStrCR_of_isCoefficientHom W₀ ι.toRingHom φ hφ hφc
  have hpb : IsPullback (Proj.map φ hφ) (projModelStrCR (W₀.map ι.toRingHom)) (projModelStrCR W₀)
      (Spec.map (CommRingCat.ofHom ι.toRingHom)) :=
    isPullback_projMap_of_isCoefficientHom W₀ ι.toRingHom φ hφ hφc

  haveI : IsSeparated (projModelStrCR (W₀ : WeierstrassCurve.Projective T)) :=
    (WeierstrassProjModel.projModelStrCR_isProper (W₀ : WeierstrassCurve.Projective T)).toIsSeparated
  haveI : IsSeparated (projModelStrCR (W₀.map ι.toRingHom : WeierstrassCurve.Projective K)) :=
    (WeierstrassProjModel.projModelStrCR_isProper (W₀.map ι.toRingHom : WeierstrassCurve.Projective K)).toIsSeparated
  haveI : IsReduced (projModelCR (W₀.map ι.toRingHom)) := isReduced_projModelCR (W₀.map ι.toRingHom) hΔ'

  have he : ((𝒢 T W₀ hΔ₀).one (𝟙 _)).1 ≫ projModelStrCR W₀ = 𝟙 _ := ((𝒢 T W₀ hΔ₀).one (𝟙 _)).2
  have heK : ((𝒢 K (W₀.map ι.toRingHom) hΔ').one (𝟙 _)).1 ≫ projModelStrCR (W₀.map ι.toRingHom) = 𝟙 _ :=
    ((𝒢 K (W₀.map ι.toRingHom) hΔ').one (𝟙 _)).2
  haveI : IsClosedImmersion ((𝒢 T W₀ hΔ₀).one (𝟙 _)).1 :=
    isClosedImmersion_of_comp_eq_id _ (projModelStrCR W₀) he
  haveI : IsClosedImmersion ((𝒢 K (W₀.map ι.toRingHom) hΔ').one (𝟙 _)).1 :=
    isClosedImmersion_of_comp_eq_id _ (projModelStrCR (W₀.map ι.toRingHom)) heK

  have hcomm : ((𝒢 K (W₀.map ι.toRingHom) hΔ').one (𝟙 _)).1 ≫ Proj.map φ hφ =
      Spec.map (CommRingCat.ofHom ι.toRingHom) ≫ ((𝒢 T W₀ hΔ₀).one (𝟙 _)).1 := by
    rw [GroupLaws.one_comp_projMap_eq_of_isCoefficientHom A 𝒢 h𝒢O T K ι W₀ hΔ₀ hΔ' φ hφ hφc (𝟙 _)]
    exact (congrArg Subtype.val ((𝒢 T W₀ hΔ₀).one_natural (𝟙 _)
      (𝟙 _ ≫ Spec.map (CommRingCat.ofHom ι.toRingHom)) (Spec.map (CommRingCat.ofHom ι.toRingHom))
      (by simp))).symm

  have hB : ((𝒢 K (W₀.map ι.toRingHom) hΔ').one (𝟙 _)).1.ker =
      ((𝒢 T W₀ hΔ₀).one (𝟙 _)).1.ker.comap (Proj.map φ hφ) :=
    ker_eq_comap_of_isPullback _ (projModelStrCR W₀) _ (projModelStrCR (W₀.map ι.toRingHom)) (Proj.map φ hφ)
      (Spec.map (CommRingCat.ofHom ι.toRingHom)) he heK hpb hcomm

  have hC : (𝒢 K (W₀.map ι.toRingHom) hΔ').schemeNsmul n ≫ Proj.map φ hφ =
      Proj.map φ hφ ≫ (𝒢 T W₀ hΔ₀).schemeNsmul n :=
    schemeNsmul_comp_eq_comp_schemeNsmul W₀ ι.toRingHom φ hφ hsq (𝒢 T W₀ hΔ₀)
      (𝒢 K (W₀.map ι.toRingHom) hΔ')
      (fun s => GroupLaws.one_comp_projMap_eq_of_isCoefficientHom A 𝒢 h𝒢O T K ι W₀ hΔ₀ hΔ' φ hφ hφc s)
      (fun F _ _ x y x' y' hx hy =>
        GroupLaws.mul_comp_projMap_eq_at_field_of_isCoefficientHom A 𝒢 h𝒢 h𝒢O T K ι W₀ hΔ₀ hΔ' φ hφ hφc
          F x y x' y' hx hy)
      n

  have hvu : pullback.fst (projModelStrCR W₀) (𝟙 (Spec (CommRingCat.of T))) ≫ toPullbackId = 𝟙 _ := by
    have huv : (toPullbackId : projModelCR W₀ ⟶ _) ≫ pullback.fst (projModelStrCR W₀) (𝟙 _) = 𝟙 _ :=
      pullback.lift_fst _ _ _
    rw [← cancel_mono (pullback.fst (projModelStrCR W₀) (𝟙 (Spec (CommRingCat.of T)))), Category.assoc, huv,
      Category.comp_id, Category.id_comp]
  have hvuK : pullback.fst (projModelStrCR (W₀.map ι.toRingHom)) (𝟙 (Spec (CommRingCat.of K))) ≫ toPullbackId =
      𝟙 _ := by
    have huv : (toPullbackId : projModelCR (W₀.map ι.toRingHom) ⟶ _) ≫
        pullback.fst (projModelStrCR (W₀.map ι.toRingHom)) (𝟙 _) = 𝟙 _ :=
      pullback.lift_fst _ _ _
    rw [← cancel_mono (pullback.fst (projModelStrCR (W₀.map ι.toRingHom)) (𝟙 (Spec (CommRingCat.of K)))),
      Category.assoc, huv, Category.comp_id, Category.id_comp]
  have hA : torsionIdeal (𝒢 T W₀ hΔ₀) n =
      ((𝒢 T W₀ hΔ₀).one (𝟙 _)).1.ker.comap
        (pullback.fst (projModelStrCR W₀) (𝟙 _) ≫ (𝒢 T W₀ hΔ₀).schemeNsmul n) :=
    ker_fst_comp_eq_comap _ _ _ _ hvu
  have hAK : torsionIdeal (𝒢 K (W₀.map ι.toRingHom) hΔ') n =
      ((𝒢 K (W₀.map ι.toRingHom) hΔ').one (𝟙 _)).1.ker.comap
        (pullback.fst (projModelStrCR (W₀.map ι.toRingHom)) (𝟙 _) ≫
          (𝒢 K (W₀.map ι.toRingHom) hΔ').schemeNsmul n) :=
    ker_fst_comp_eq_comap _ _ _ _ hvuK

  have hmor : pullback.fst (pullback.snd (projModelStrCR W₀) (𝟙 _)) (Spec.map (CommRingCat.ofHom ι.toRingHom)) ≫
        pullback.fst (projModelStrCR W₀) (𝟙 _) ≫ (𝒢 T W₀ hΔ₀).schemeNsmul n =
      θ ≫ pullback.fst (projModelStrCR (W₀.map ι.toRingHom)) (𝟙 _) ≫
        (𝒢 K (W₀.map ι.toRingHom) hΔ').schemeNsmul n ≫ Proj.map φ hφ := by
    have h := hθ₁ =≫ (𝒢 T W₀ hΔ₀).schemeNsmul n
    simp only [Category.assoc] at h
    rw [hC, ← h]
  calc (torsionIdeal (𝒢 T W₀ hΔ₀) n).comap
        (pullback.fst (pullback.snd (projModelStrCR W₀) (𝟙 _)) (Spec.map (CommRingCat.ofHom ι.toRingHom)))
      = ((𝒢 T W₀ hΔ₀).one (𝟙 _)).1.ker.comap
          (pullback.fst (pullback.snd (projModelStrCR W₀) (𝟙 _)) (Spec.map (CommRingCat.ofHom ι.toRingHom)) ≫
            pullback.fst (projModelStrCR W₀) (𝟙 _) ≫ (𝒢 T W₀ hΔ₀).schemeNsmul n) := by
        rw [hA, ← Scheme.IdealSheafData.comap_comp]
    _ = ((𝒢 T W₀ hΔ₀).one (𝟙 _)).1.ker.comap
          (θ ≫ pullback.fst (projModelStrCR (W₀.map ι.toRingHom)) (𝟙 _) ≫
            (𝒢 K (W₀.map ι.toRingHom) hΔ').schemeNsmul n ≫ Proj.map φ hφ) := by rw [hmor]
    _ = ((((𝒢 T W₀ hΔ₀).one (𝟙 _)).1.ker.comap (Proj.map φ hφ)).comap
          (pullback.fst (projModelStrCR (W₀.map ι.toRingHom)) (𝟙 _) ≫
            (𝒢 K (W₀.map ι.toRingHom) hΔ').schemeNsmul n)).comap θ := by
        simp only [Scheme.IdealSheafData.comap_comp]
    _ = (torsionIdeal (𝒢 K (W₀.map ι.toRingHom) hΔ') n).comap θ := by rw [← hB, ← hAK]

end S_WeierstrassCurve_DrinfeldGlobal_torsionIdeal_comap_fst_eq_torsionIdeal_comap_theta
end P2MW
export P2MW.S_WeierstrassCurve_DrinfeldGlobal_torsionIdeal_comap_fst_eq_torsionIdeal_comap_theta (solution)
