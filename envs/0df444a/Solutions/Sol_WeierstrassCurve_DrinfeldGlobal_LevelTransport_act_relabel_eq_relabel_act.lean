-- Prove2me | solution 1 for WeierstrassCurve.DrinfeldGlobal.LevelTransport.act_relabel_eq_relabel_act
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/a2ae0a27-a939-52e8-818a-be1771518487

import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_ModularCurve_LevelRelabelling
import Theorems.Thm_WeierstrassProjModel_RelativeGroupLaw_mul_eq_of_one_eq_of_isElliptic
import Theorems.Thm_WeierstrassProjModel_RelativeGroupLaw_exists_relativeGroupLaw_comp_eq_of_isPullback
import Theorems.Thm_WeierstrassProjModel_RelativeGroupLaw_exists_isOriginChartSection_iff_one_eq_kwZeroSect
import Theorems.Thm_WeierstrassProjModel_kwZeroSect_comp_projMap_of_isVariableChangeHom
import Theorems.Thm_WeierstrassProjModel_exists_isVariableChangeHom_isIso_projMap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_DrinfeldGlobal_LevelTransport_act_relabel_eq_relabel_act

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal

attribute [local instance] MvPolynomial.gradedAlgebra

namespace P2MmfRelabelAct

theorem rawDrinfeldPair_ext {T : Type u} [CommRing T] (r r' : RawDrinfeldPair T) (hc : r.curve = r'.curve)
    (hP : r.P.1 ≫ eqToHom (congrArg projModelCR hc) = r'.P.1)
    (hQ : r.Q.1 ≫ eqToHom (congrArg projModelCR hc) = r'.Q.1) : r = r' := by
  obtain ⟨c, P, Q⟩ := r
  obtain ⟨c', P', Q'⟩ := r'
  dsimp only at hc
  subst hc
  simp only [eqToHom_refl, Category.comp_id] at hP hQ
  cases Subtype.ext hP
  cases Subtype.ext hQ
  rfl

theorem section_eq_of_mono {T : Type u} [CommRing T] (V : WeierstrassCurve.Projective T)
    {c c' : WeierstrassCurve.Projective T} (e : c = V) (e' : c' = V)
    (P : Section c) (P' : Section c') {Z : Scheme.{u}} (g : projModelCR V ⟶ Z) [Mono g]
    (h : P.1 ≫ eqToHom (congrArg projModelCR e) ≫ g = P'.1 ≫ eqToHom (congrArg projModelCR e') ≫ g) :
    P.1 ≫ eqToHom (congrArg projModelCR (e.trans e'.symm)) = P'.1 := by
  subst e
  subst e'
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at h ⊢
  exact (cancel_mono g).mp h

theorem mul_val_congr {R : Type u} [CommRing R] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)}
    (G : RelativeGroupLaw R f) {S : Scheme.{u}} {s s' : S ⟶ Spec (CommRingCat.of R)} (e : s = s')
    (x y : SchemeHomOver s f) (x' y' : SchemeHomOver s' f) (hx : x.1 = x'.1) (hy : y.1 = y'.1) :
    (G.mul s x y).1 = (G.mul s' x' y').1 := by
  subst e
  cases Subtype.ext hx
  cases Subtype.ext hy
  rfl

theorem inv_val_congr {R : Type u} [CommRing R] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)}
    (G : RelativeGroupLaw R f) {S : Scheme.{u}} {s s' : S ⟶ Spec (CommRingCat.of R)} (e : s = s')
    (x : SchemeHomOver s f) (x' : SchemeHomOver s' f) (hx : x.1 = x'.1) :
    (G.inv s x).1 = (G.inv s' x').1 := by
  subst e
  cases Subtype.ext hx
  rfl

theorem inv_natural {R : Type u} [CommRing R] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)}
    (G : RelativeGroupLaw R f) {S S' : Scheme.{u}} (t : S ⟶ Spec (CommRingCat.of R))
    (t' : S' ⟶ Spec (CommRingCat.of R)) (ψ : S' ⟶ S) (hψ : ψ ≫ t = t') (x : SchemeHomOver t f) :
    schemeHomOverComp ψ hψ (G.inv t x) = G.inv t' (schemeHomOverComp ψ hψ x) := by
  letI : Group (SchemeHomOver t' f) := G.pointGroup t'
  have h : schemeHomOverComp ψ hψ (G.inv t x) * schemeHomOverComp ψ hψ x = 1 := by
    show G.mul t' _ _ = G.one t'
    rw [← G.mul_natural t t' ψ hψ, G.inv_mul_cancel, G.one_natural]
  exact eq_inv_of_mul_eq_one_left h

theorem zlinComb_comp_of_mul_comp {T T' : Type u} [CommRing T] [CommRing T']
    (V : WeierstrassCurve.Projective T) (V' : WeierstrassCurve.Projective T') (f : T →+* T')
    (π : projModelCR V' ⟶ projModelCR V)
    (hsq : π ≫ projModelStrCR V = projModelStrCR V' ≫ Spec.map (CommRingCat.ofHom f))
    (G : RelativeGroupLaw T (projModelStrCR V)) (L : RelativeGroupLaw T' (projModelStrCR V'))
    (hmul : ∀ x y : Section V', (L.mul (𝟙 _) x y).1 ≫ π =
      (G.mul (𝟙 _ ≫ Spec.map (CommRingCat.ofHom f))
        ⟨x.1 ≫ π, by rw [Category.assoc, hsq, ← Category.assoc, x.2]⟩
        ⟨y.1 ≫ π, by rw [Category.assoc, hsq, ← Category.assoc, y.2]⟩).1)
    (h1 : (L.one (𝟙 (Spec (CommRingCat.of T')))).1 ≫ π =
      Spec.map (CommRingCat.ofHom f) ≫ (G.one (𝟙 (Spec (CommRingCat.of T)))).1)
    (Py Qy : Section V') (P Q : Section V)
    (hP : Py.1 ≫ π = Spec.map (CommRingCat.ofHom f) ≫ P.1)
    (hQ : Qy.1 ≫ π = Spec.map (CommRingCat.ofHom f) ≫ Q.1) (a b : ℤ) :
    (ModularCurve.LevelRelabelling.zlinComb L Py Qy a b).1 ≫ π =
      Spec.map (CommRingCat.ofHom f) ≫ (ModularCurve.LevelRelabelling.zlinComb G P Q a b).1 := by
  set t : Spec (CommRingCat.of T') ⟶ Spec (CommRingCat.of T) :=
    𝟙 (Spec (CommRingCat.of T')) ≫ Spec.map (CommRingCat.ofHom f) with ht
  have hψ : Spec.map (CommRingCat.ofHom f) ≫ 𝟙 (Spec (CommRingCat.of T)) = t := by
    rw [ht, Category.comp_id, Category.id_comp]
  let bc : Section V → SchemeHomOver t (projModelStrCR V) := fun s => schemeHomOverComp _ hψ s
  have hbc : ∀ s : Section V, (bc s).1 = Spec.map (CommRingCat.ofHom f) ≫ s.1 := fun s => rfl
  let im : Section V' → SchemeHomOver t (projModelStrCR V) := fun s =>
    ⟨s.1 ≫ π, by rw [Category.assoc, hsq, ← Category.assoc, s.2]⟩
  have him : ∀ s : Section V', (im s).1 = s.1 ≫ π := fun s => rfl
  have hmul' : ∀ x y : Section V', im (L.mul _ x y) = G.mul t (im x) (im y) := by
    intro x y
    apply Subtype.ext
    exact hmul x y
  have hone : im (L.one _) = G.one t := by
    apply Subtype.ext
    rw [him, h1, ← hbc (G.one _)]
    exact congrArg Subtype.val (G.one_natural (𝟙 _) t _ hψ)
  have hnsmul : ∀ (n : ℕ) (x : Section V'), im (L.nsmul _ n x) = G.nsmul t n (im x) := by
    intro n x
    induction n with
    | zero => rw [L.nsmul_zero, G.nsmul_zero]; exact hone
    | succ n ih => rw [L.nsmul_succ, G.nsmul_succ, hmul', ih]
  have hinv : ∀ x : Section V', im (L.inv _ x) = G.inv t (im x) := by
    intro x
    letI : Group (SchemeHomOver t (projModelStrCR V)) := G.pointGroup t
    have h : im (L.inv _ x) * im x = 1 := by
      show G.mul t _ _ = G.one t
      rw [← hmul', L.inv_mul_cancel, hone]
    exact eq_inv_of_mul_eq_one_left h
  have hzsmul : ∀ (n : ℤ) (x : Section V') (s : Section V), im x = bc s →
      im (ModularCurve.LevelRelabelling.zsmulSection L n x) = bc (ModularCurve.LevelRelabelling.zsmulSection G n s) := by
    intro n x s hx
    cases n with
    | ofNat k =>
      show im (L.nsmul _ k x) = bc (G.nsmul _ k s)
      rw [hnsmul, hx]
      exact (G.nsmul_natural (𝟙 _) t _ hψ k s).symm
    | negSucc k =>
      show im (L.inv _ (L.nsmul _ (k + 1) x)) = bc (G.inv _ (G.nsmul _ (k + 1) s))
      rw [hinv, hnsmul, hx, ← G.nsmul_natural (𝟙 _) t _ hψ (k + 1) s]
      exact (inv_natural G (𝟙 _) t _ hψ _).symm
  have hPim : im Py = bc P := Subtype.ext (by rw [him, hbc]; exact hP)
  have hQim : im Qy = bc Q := Subtype.ext (by rw [him, hbc]; exact hQ)
  have key : im (ModularCurve.LevelRelabelling.zlinComb L Py Qy a b) =
      bc (ModularCurve.LevelRelabelling.zlinComb G P Q a b) := by
    show im (L.mul _ (ModularCurve.LevelRelabelling.zsmulSection L a Py) (ModularCurve.LevelRelabelling.zsmulSection L b Qy)) =
      bc (G.mul _ (ModularCurve.LevelRelabelling.zsmulSection G a P) (ModularCurve.LevelRelabelling.zsmulSection G b Q))
    rw [hmul', hzsmul a Py P hPim, hzsmul b Qy Q hQim]
    exact (G.mul_natural (𝟙 _) t _ hψ _ _).symm
  have := congrArg Subtype.val key
  rw [him, hbc] at this
  exact this

theorem eq_relabel_of_pins_act {A : Type} [CommRing A] (𝒢 : GroupLaws A)
    {T : Type} [CommRing T] [Algebra A T]
    (V : WeierstrassCurve.Projective T) (hΔ : IsUnit V.Δ) (C : WeierstrassCurve.VariableChange T) (hΔC : IsUnit (C • V).Δ)
    (π : projModelCR (C • V) ⟶ projModelCR V) [Mono π]
    (hzlin : ∀ (Py Qy : Section (C • V)) (P Q : Section V),
      Py.1 ≫ π = P.1 → Qy.1 ≫ π = Q.1 → ∀ a b : ℤ,
        (ModularCurve.LevelRelabelling.zlinComb (𝒢 T (C • V) hΔC) Py Qy a b).1 ≫ π =
          (ModularCurve.LevelRelabelling.zlinComb (𝒢 T V hΔ) P Q a b).1)
    (P Q : Section V) (g : Matrix (Fin 2) (Fin 2) ℤ)
    (y yg : RawDrinfeldPair T) (hc : y.curve = C • V) (hΔ' : IsUnit y.curve.Δ)
    (hP : y.P.1 ≫ eqToHom (congrArg projModelCR hc) ≫ π = P.1)
    (hQ : y.Q.1 ≫ eqToHom (congrArg projModelCR hc) ≫ π = Q.1)
    (hcg : yg.curve = C • V)
    (hPg : yg.P.1 ≫ eqToHom (congrArg projModelCR hcg) ≫ π =
      (ModularCurve.LevelRelabelling.zlinComb (𝒢 T V hΔ) P Q (g 0 0) (g 1 0)).1)
    (hQg : yg.Q.1 ≫ eqToHom (congrArg projModelCR hcg) ≫ π =
      (ModularCurve.LevelRelabelling.zlinComb (𝒢 T V hΔ) P Q (g 0 1) (g 1 1)).1) :
    yg = ModularCurve.LevelRelabelling.RawDrinfeldPair.relabel 𝒢 g y hΔ' := by
  obtain ⟨c, Py, Qy⟩ := y
  dsimp only at hc
  subst c
  simp only [eqToHom_refl, Category.id_comp] at hP hQ
  unfold ModularCurve.LevelRelabelling.RawDrinfeldPair.relabel
  dsimp only
  refine rawDrinfeldPair_ext _ _ hcg ?_ ?_
  · refine section_eq_of_mono (C • V) hcg rfl yg.P
      (ModularCurve.LevelRelabelling.zlinComb (𝒢 T (C • V) hΔC) Py Qy (g 0 0) (g 1 0)) π ?_
    rw [hPg]
    simp only [eqToHom_refl, Category.id_comp]
    exact (hzlin Py Qy P Q hP hQ (g 0 0) (g 1 0)).symm
  · refine section_eq_of_mono (C • V) hcg rfl yg.Q
      (ModularCurve.LevelRelabelling.zlinComb (𝒢 T (C • V) hΔC) Py Qy (g 0 1) (g 1 1)) π ?_
    rw [hQg]
    simp only [eqToHom_refl, Category.id_comp]
    exact (hzlin Py Qy P Q hP hQ (g 0 1) (g 1 1)).symm

end P2MmfRelabelAct

open P2MmfRelabelAct

theorem solution
    {A : Type} [CommRing A] (𝒢 : GroupLaws A) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)
    (q : ℕ) (𝒯 : LevelTransport A 𝒢 q) (h𝒯 : 𝒯.IsSectionTransport)
    (hVC : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve.Projective T) (C : WeierstrassCurve.VariableChange T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (C • W))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (C • W)) ≤ (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
        IsVariableChangeHom W C φ)
    (hCO : ∀ (T T' : Type) [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] (f : T →ₐ[A] T')
      (W : WeierstrassCurve.Projective T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (W.map f.toRingHom))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map f.toRingHom)) ≤
          (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
        IsCoefficientHom W f.toRingHom φ)
    (T : Type) [CommRing T] [Algebra A T] (C : WeierstrassCurve.VariableChange T)
    (g : Matrix (Fin 2) (Fin 2) ℤ) (x : RawDrinfeldPair T) (hΔ : IsUnit x.curve.Δ) (hΔ' : IsUnit (𝒯.act C x).curve.Δ) :
    𝒯.act C (ModularCurve.LevelRelabelling.RawDrinfeldPair.relabel 𝒢 g x hΔ) =
      ModularCurve.LevelRelabelling.RawDrinfeldPair.relabel 𝒢 g (𝒯.act C x) hΔ' := by
  obtain ⟨V, P, Q⟩ := x
  change IsUnit V.Δ at hΔ

  obtain ⟨φ, hφ, hvc, hiso, hπ⟩ := WeierstrassProjModel.exists_isVariableChangeHom_isIso_projMap V C
  haveI := hiso

  obtain ⟨hc, H⟩ := h𝒯.1 T C ⟨V, P, Q⟩
  obtain ⟨hcg, Hg⟩ := h𝒯.1 T C (ModularCurve.LevelRelabelling.RawDrinfeldPair.relabel 𝒢 g ⟨V, P, Q⟩ hΔ)
  obtain ⟨hP, hQ⟩ := H φ hφ hvc
  obtain ⟨hPg, hQg⟩ := Hg φ hφ hvc

  haveI hE : V.toAffine.IsElliptic := ⟨hΔ⟩
  have hΔC : IsUnit (C • V).Δ := by
    rw [WeierstrassCurve.variableChange_Δ]
    exact ((C.u⁻¹).isUnit.pow 12).mul hΔ
  haveI hE' : (C • V).toAffine.IsElliptic := ⟨hΔC⟩

  have hid : Spec.map (CommRingCat.ofHom (RingHom.id T)) = 𝟙 (Spec (CommRingCat.of T)) := by
    rw [CommRingCat.ofHom_id]; exact Spec.map_id _
  haveI : IsIso (Spec.map (CommRingCat.ofHom (RingHom.id T))) := by rw [hid]; infer_instance
  have hsq : Proj.map φ hφ ≫ projModelStrCR V =
      projModelStrCR (C • V) ≫ Spec.map (CommRingCat.ofHom (RingHom.id T)) := by
    rw [hid, Category.comp_id]; exact hπ
  have hpb : IsPullback (Proj.map φ hφ) (projModelStrCR (C • V)) (projModelStrCR V)
      (Spec.map (CommRingCat.ofHom (RingHom.id T))) := IsPullback.of_horiz_isIso ⟨hsq⟩

  obtain ⟨Gh, hGh_mul, hGh_one⟩ := RelativeGroupLaw.exists_relativeGroupLaw_comp_eq_of_isPullback (RingHom.id T)
    (projModelStrCR V) (projModelStrCR (C • V)) (Proj.map φ hφ) hpb (𝒢 T V hΔ)
  have hG1 : ((𝒢 T V hΔ).one (𝟙 _)).1 = (kwZeroSect T V).1 :=
    (RelativeGroupLaw.exists_isOriginChartSection_iff_one_eq_kwZeroSect V (𝒢 T V hΔ)).mp (h𝒢O T V hΔ)
  have hG'1 : ((𝒢 T (C • V) hΔC).one (𝟙 _)).1 = (kwZeroSect T (C • V)).1 :=
    (RelativeGroupLaw.exists_isOriginChartSection_iff_one_eq_kwZeroSect (C • V) (𝒢 T (C • V) hΔC)).mp
      (h𝒢O T (C • V) hΔC)
  have hz : (kwZeroSect T (C • V)).1 ≫ Proj.map φ hφ = (kwZeroSect T V).1 :=
    WeierstrassProjModel.kwZeroSect_comp_projMap_of_isVariableChangeHom V C φ hφ hvc
  have h1' : ((𝒢 T (C • V) hΔC).one (𝟙 _)).1 ≫ Proj.map φ hφ = ((𝒢 T V hΔ).one (𝟙 _)).1 := by
    rw [hG'1, hz, hG1]
  have hbase : (𝟙 _ ≫ Spec.map (CommRingCat.ofHom (RingHom.id T))) = 𝟙 (Spec (CommRingCat.of T)) := by
    rw [hid, Category.comp_id]
  have hGh1 : (Gh.one (𝟙 _)).1 ≫ Proj.map φ hφ = ((𝒢 T V hΔ).one (𝟙 _)).1 := by
    rw [hGh_one, hbase]
  have hone_eq : ((𝒢 T (C • V) hΔC).one (𝟙 _)).1 = (Gh.one (𝟙 _)).1 :=
    (cancel_mono (Proj.map φ hφ)).mp (h1'.trans hGh1.symm)
  have hmulEq : ∀ x y : Section (C • V), (𝒢 T (C • V) hΔC).mul (𝟙 _) x y = Gh.mul (𝟙 _) x y := fun x y =>
    RelativeGroupLaw.mul_eq_of_one_eq_of_isElliptic (C • V) (𝒢 T (C • V) hΔC) Gh hone_eq (𝟙 _) x y
  have h1 : ((𝒢 T (C • V) hΔC).one (𝟙 (Spec (CommRingCat.of T)))).1 ≫ Proj.map φ hφ =
      Spec.map (CommRingCat.ofHom (RingHom.id T)) ≫ ((𝒢 T V hΔ).one (𝟙 (Spec (CommRingCat.of T)))).1 := by
    rw [h1', hid, Category.id_comp]
  have hzlin : ∀ (Py Qy : Section (C • V)) (P Q : Section V),
      Py.1 ≫ Proj.map φ hφ = P.1 → Qy.1 ≫ Proj.map φ hφ = Q.1 → ∀ a b : ℤ,
        (ModularCurve.LevelRelabelling.zlinComb (𝒢 T (C • V) hΔC) Py Qy a b).1 ≫ Proj.map φ hφ =
          (ModularCurve.LevelRelabelling.zlinComb (𝒢 T V hΔ) P Q a b).1 := by
    intro Py Qy P' Q' hP' hQ' a b
    have h := zlinComb_comp_of_mul_comp V (C • V) (RingHom.id T) (Proj.map φ hφ) hsq (𝒢 T V hΔ) (𝒢 T (C • V) hΔC)
      (fun x y => by rw [hmulEq]; exact hGh_mul (𝟙 _) x y) h1 Py Qy P' Q'
      (by rw [hP', hid, Category.id_comp]) (by rw [hQ', hid, Category.id_comp]) a b
    rw [hid, Category.id_comp] at h
    exact h
  exact eq_relabel_of_pins_act 𝒢 V hΔ C hΔC (Proj.map φ hφ) hzlin P Q g (𝒯.act C ⟨V, P, Q⟩)
    (𝒯.act C (ModularCurve.LevelRelabelling.RawDrinfeldPair.relabel 𝒢 g ⟨V, P, Q⟩ hΔ)) hc hΔ' hP hQ hcg hPg hQg

end S_WeierstrassCurve_DrinfeldGlobal_LevelTransport_act_relabel_eq_relabel_act
end P2MW
export P2MW.S_WeierstrassCurve_DrinfeldGlobal_LevelTransport_act_relabel_eq_relabel_act (solution)
