-- Prove2me | solution 1 for WeierstrassCurve.DrinfeldGlobal.nsmul_eq_one_of_specMap_fstHom_comp_eq_of_nsmul_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/566cedfa-6723-50ae-98ef-6ae909d12301

import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor

import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_nsmul_eq_one_of_sqZero_of_natCast_eq_zero
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_GroupLaws_mul_comm_of_isOriginIdentity
import Theorems.Thm_WeierstrassProjModel_exists_isCoefficientHom
import Theorems.Thm_WeierstrassProjModel_exists_isVariableChangeHom_isIso_projMap
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_isPullback_projMap_of_isCoefficientHom
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_comp_projMap_eq_of_isOriginChartSection
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_comp_projMap_mul_eq_mul_comp_projMap_of_one_comp_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_DrinfeldGlobal_nsmul_eq_one_of_specMap_fstHom_comp_eq_of_nsmul_eq_one
p2m_attr_erase "simp" "WeierstrassProjModel.kw_lrThird_substHom_X GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left"

set_option autoImplicit false
p2m_open "AlgebraicGeometry CategoryTheory NeronModelInfra WeierstrassProjModel P2MW.S_WeierstrassCurve_DrinfeldGlobal_nsmul_eq_one_of_specMap_fstHom_comp_eq_of_nsmul_eq_one.WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal IsLocalRing FormalGroup"
attribute [local instance] MvPolynomial.gradedAlgebra

universe u

namespace WeierstrassProjModel
p2m_export "WeierstrassProjModel" "schemeHomOverComp schemeHomOverComp_coe RelativeGroupLaw RelativeGroupLaw.nsmul_succ projModelGradingCR projModelStrCR exists_isCoefficientHom exists_isVariableChangeHom_isIso_projMap"
namespace RelativeGroupLaw
p2m_export "WeierstrassProjModel.RelativeGroupLaw" "nsmul nsmul_succ pointGroup one_natural nsmul_natural mul_one inv_mul_cancel mul_assoc one_mul inv mul mul_natural one"
p2m_open "WeierstrassProjModel.RelativeGroupLaw WeierstrassProjModel"

variable {R : Type u} [CommRing R] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)}

private def _root_.WeierstrassProjModel.RelativeGroupLaw.toGRJ (G : RelativeGroupLaw R f) : GoodReductionJacobian.RelativeGroupLaw R f where
  mul := G.mul
  one := G.one
  inv := G.inv
  mul_assoc := G.mul_assoc
  one_mul := G.one_mul
  mul_one := G.mul_one
  inv_mul_cancel := G.inv_mul_cancel
  mul_natural := fun t t' ψ hψ x y => G.mul_natural t t' ψ hψ x y

p2m_export "WeierstrassProjModel.RelativeGroupLaw" "toGRJ"
theorem toGRJ_nsmul (G : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ)
    (x : SchemeHomOver t f) : G.toGRJ.nsmul t n x = G.nsmul t n x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [GoodReductionJacobian.RelativeGroupLaw.nsmul_succ, nsmul_succ, ih]
    rfl

end WeierstrassProjModel.RelativeGroupLaw

namespace LiftIsTorsionAux

p2m_open "WeierstrassProjModel P2MW.S_WeierstrassCurve_DrinfeldGlobal_nsmul_eq_one_of_specMap_fstHom_comp_eq_of_nsmul_eq_one.WeierstrassProjModel"

theorem exists_section_comp_projMap
    {B T' : Type} [CommRing B] [CommRing T'] (V : WeierstrassCurve B) (g : B →+* T')
    (φ : projModelGradingCR V →+*ᵍ projModelGradingCR (V.map g))
    (hφ : HomogeneousIdeal.irrelevant (projModelGradingCR (V.map g)) ≤
      (HomogeneousIdeal.irrelevant (projModelGradingCR V)).map φ)
    (hcoef : IsCoefficientHom V g φ)
    (y : SchemeHomOver (Spec.map (CommRingCat.ofHom g)) (projModelStrCR V)) :
    ∃ y' : Section (V.map g), y'.1 ≫ Proj.map φ hφ = y.1 := by
  have hpb := WeierstrassCurve.DrinfeldGlobal.isPullback_projMap_of_isCoefficientHom V g φ hφ hcoef
  have w : y.1 ≫ projModelStrCR V = 𝟙 _ ≫ Spec.map (CommRingCat.ofHom g) := by
    rw [Category.id_comp]; exact y.2
  exact ⟨⟨hpb.lift y.1 (𝟙 _) w, hpb.lift_snd _ _ _⟩, hpb.lift_fst _ _ _⟩

theorem mul_comm_specMap
    {A : Type} [CommRing A] (𝒢 : GroupLaws A) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)
    (B : Type) [CommRing B] [Algebra A B] (V : WeierstrassCurve B) (hΔ : IsUnit V.Δ)
    {T' : Type} [CommRing T'] (g : B →+* T')
    (y z : SchemeHomOver (Spec.map (CommRingCat.ofHom g)) (projModelStrCR V)) :
    (𝒢 B V hΔ).mul _ y z = (𝒢 B V hΔ).mul _ z y := by
  classical
  letI algA : Algebra A T' := (g.comp (algebraMap A B)).toAlgebra
  have hΔ' : IsUnit (V.map g).Δ := by rw [WeierstrassCurve.map_Δ]; exact hΔ.map _
  obtain ⟨φ, hφ, hcoef⟩ := WeierstrassProjModel.exists_isCoefficientHom V g
  have hsq : Proj.map φ hφ ≫ projModelStrCR V = projModelStrCR (V.map g) ≫ Spec.map (CommRingCat.ofHom g) :=
    (WeierstrassCurve.DrinfeldGlobal.isPullback_projMap_of_isCoefficientHom V g φ hφ hcoef).w
  haveI : V.toAffine.IsElliptic := ⟨hΔ⟩

  obtain ⟨χ, hχ, hχx, hχz⟩ := h𝒢O B V hΔ
  obtain ⟨χ', hχ', hχ'x, hχ'z⟩ := h𝒢O T' (V.map g) hΔ'
  have h1 := WeierstrassCurve.DrinfeldGlobal.comp_projMap_eq_of_isOriginChartSection V g φ hφ hcoef
    ((𝒢 B V hΔ).one (𝟙 _)) ((𝒢 T' (V.map g) hΔ').one (𝟙 _)) χ hχ hχx hχz χ' hχ' hχ'x hχ'z

  have hVC' : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve.Projective T) (C : WeierstrassCurve.VariableChange T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (C • W))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (C • W)) ≤ (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
        IsVariableChangeHom W C φ := by
    intro T _ _ W C
    obtain ⟨φ₁, hφ₁, hV, -, -⟩ := WeierstrassProjModel.exists_isVariableChangeHom_isIso_projMap W C
    exact ⟨φ₁, hφ₁, hV⟩
  have hCO' : ∀ (T T'' : Type) [CommRing T] [Algebra A T] [CommRing T''] [Algebra A T''] (f : T →ₐ[A] T'')
      (W : WeierstrassCurve.Projective T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (W.map f.toRingHom))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map f.toRingHom)) ≤
          (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
        IsCoefficientHom W f.toRingHom φ :=
    fun T T'' _ _ _ _ f₁ W => WeierstrassProjModel.exists_isCoefficientHom W f₁.toRingHom
  have hLcomm := WeierstrassCurve.DrinfeldGlobal.GroupLaws.mul_comm_of_isOriginIdentity 𝒢 h𝒢 h𝒢O hVC' hCO'
    T' (V.map g) hΔ'

  have key := fun (a b : Section (V.map g)) =>
    WeierstrassCurve.DrinfeldGlobal.comp_projMap_mul_eq_mul_comp_projMap_of_one_comp_eq V g φ hφ hcoef
      (𝒢 B V hΔ) (𝒢 T' (V.map g) hΔ') h1 hsq (𝟙 _) a b
  obtain ⟨y', hy'⟩ := exists_section_comp_projMap V g φ hφ hcoef y
  obtain ⟨z', hz'⟩ := exists_section_comp_projMap V g φ hφ hcoef z
  have k1 := key y' z'
  have k2 := key z' y'
  rw [hLcomm y' z'] at k1
  have mid := k1.symm.trans k2

  apply Subtype.ext
  have e : ∀ a b : SchemeHomOver (Spec.map (CommRingCat.ofHom g)) (projModelStrCR V),
      ((𝒢 B V hΔ).mul _ a b).1 =
        ((𝒢 B V hΔ).mul (𝟙 _ ≫ Spec.map (CommRingCat.ofHom g)) (schemeHomOverComp (𝟙 _) rfl a)
          (schemeHomOverComp (𝟙 _) rfl b)).1 := by
    intro a b
    rw [← (𝒢 B V hΔ).mul_natural _ (𝟙 _ ≫ Spec.map (CommRingCat.ofHom g)) (𝟙 _) rfl a b, schemeHomOverComp_coe,
      Category.id_comp]
  have hcy : schemeHomOverComp (𝟙 _) (rfl : 𝟙 _ ≫ Spec.map (CommRingCat.ofHom g) = _) y =
      (⟨y'.1 ≫ Proj.map φ hφ, by rw [Category.assoc, hsq, ← Category.assoc, y'.2]⟩ :
        SchemeHomOver (𝟙 _ ≫ Spec.map (CommRingCat.ofHom g)) (projModelStrCR V)) := by
    apply Subtype.ext
    show 𝟙 _ ≫ y.1 = y'.1 ≫ Proj.map φ hφ
    rw [Category.id_comp, hy']
  have hcz : schemeHomOverComp (𝟙 _) (rfl : 𝟙 _ ≫ Spec.map (CommRingCat.ofHom g) = _) z =
      (⟨z'.1 ≫ Proj.map φ hφ, by rw [Category.assoc, hsq, ← Category.assoc, z'.2]⟩ :
        SchemeHomOver (𝟙 _ ≫ Spec.map (CommRingCat.ofHom g)) (projModelStrCR V)) := by
    apply Subtype.ext
    show 𝟙 _ ≫ z.1 = z'.1 ≫ Proj.map φ hφ
    rw [Category.id_comp, hz']
  rw [e y z, e z y, hcy, hcz]
  exact mid

end LiftIsTorsionAux

theorem solution
    (A : Type) [CommRing A] (𝒢 : GroupLaws A) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity) (q : ℕ)
    (B : Type) [CommRing B] [Algebra A B] (V : WeierstrassCurve B) (hΔ : IsUnit V.Δ)
    (k : Type) [Field k] [CharP k q] (f : B →+* k)
    (Q₀ : SchemeHomOver (Spec.map (CommRingCat.ofHom f)) (projModelStrCR V))
    (hQ₀ : (𝒢 B V hΔ).nsmul _ q Q₀ = (𝒢 B V hΔ).one _)
    (Q : SchemeHomOver (Spec.map (CommRingCat.ofHom ((algebraMap k (DualNumber k)).comp f))) (projModelStrCR V))
    (hQ : Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom) ≫ Q.1 = Q₀.1) :
    (𝒢 B V hΔ).nsmul _ q Q = (𝒢 B V hΔ).one _ := by
  classical
  set G := 𝒢 B V hΔ with hG

  let t₀ : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of B) := Spec.map (CommRingCat.ofHom f)
  let t : Spec (CommRingCat.of (DualNumber k)) ⟶ Spec (CommRingCat.of B) :=
    Spec.map (CommRingCat.ofHom ((algebraMap k (DualNumber k)).comp f))
  let ι : Spec (CommRingCat.of (DualNumber k)) ⟶ Spec (CommRingCat.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k)))
  let π : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (DualNumber k)) :=
    Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom)
  have hι : ι ≫ t₀ = t := by
    simp only [t, t₀, ι, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have hfst : (TrivSqZeroExt.fstHom k k k).toRingHom.comp (algebraMap k (DualNumber k)) = RingHom.id k := by
    ext a; rfl
  have hπι : π ≫ ι = 𝟙 _ := by
    simp only [π, ι, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hfst, CommRingCat.ofHom_id, Spec.map_id]

  let Q₀' : SchemeHomOver t (projModelStrCR V) := schemeHomOverComp ι hι Q₀
  have hQ₀' : G.nsmul t q Q₀' = G.one t := by
    show G.nsmul t q (schemeHomOverComp ι hι Q₀) = G.one t
    rw [← G.nsmul_natural t₀ t ι hι, hQ₀, G.one_natural]

  letI grpT : Group (SchemeHomOver t (projModelStrCR V)) := G.pointGroup t
  letI grp0 : Group (SchemeHomOver (π ≫ t) (projModelStrCR V)) := G.pointGroup (π ≫ t)
  let res : SchemeHomOver t (projModelStrCR V) →* SchemeHomOver (π ≫ t) (projModelStrCR V) :=
    { toFun := fun y => schemeHomOverComp π rfl y
      map_one' := G.one_natural t _ π rfl
      map_mul' := fun y z => G.mul_natural t _ π rfl y z }
  have hres : ∀ y, res y = schemeHomOverComp π rfl y := fun _ => rfl
  have hresQ : res Q = res Q₀' := by
    apply Subtype.ext
    show π ≫ Q.1 = π ≫ (ι ≫ Q₀.1)
    rw [hQ, ← Category.assoc, hπι, Category.id_comp]

  let x : SchemeHomOver t (projModelStrCR V) := Q * Q₀'⁻¹
  have hx : GoodReductionJacobian.schemeHomOverComp π rfl x = G.toGRJ.one (π ≫ t) := by
    show res (Q * Q₀'⁻¹) = 1
    rw [map_mul, map_inv, hresQ, mul_inv_cancel]

  have hsurj : Function.Surjective (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom).hom :=
    fun a => ⟨TrivSqZeroExt.inl a, rfl⟩
  have hker : RingHom.ker (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom).hom ^ 2 = ⊥ := by
    rw [pow_two, eq_bot_iff, Ideal.mul_le]
    intro a ha b hb
    rw [RingHom.mem_ker] at ha hb
    change a.fst = 0 at ha
    change b.fst = 0 at hb
    rw [Ideal.mem_bot]
    refine TrivSqZeroExt.ext ?_ ?_
    · rw [TrivSqZeroExt.fst_mul, ha, zero_mul, TrivSqZeroExt.fst_zero]
    · rw [DualNumber.snd_mul, ha, hb, zero_mul, mul_zero, _root_.add_zero, TrivSqZeroExt.snd_zero]
  have hq0 : ((q : ℕ) : (CommRingCat.of (DualNumber k) : Type)) = 0 := by
    show ((q : ℕ) : DualNumber k) = 0
    rw [← map_natCast (algebraMap k (DualNumber k)), CharP.cast_eq_zero, map_zero]
  have hxq : G.nsmul t q x = G.one t := by
    rw [← WeierstrassProjModel.RelativeGroupLaw.toGRJ_nsmul]
    exact GoodReductionJacobian.RelativeGroupLaw.nsmul_eq_one_of_sqZero_of_natCast_eq_zero G.toGRJ q
      (CommRingCat.of (DualNumber k)) (CommRingCat.of k) (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom)
      hsurj hker hq0 t x hx

  have hpow : ∀ (n : ℕ) (y : SchemeHomOver t (projModelStrCR V)), G.nsmul t n y = y ^ n := by
    intro n y
    induction n with
    | zero => rfl
    | succ n ih => rw [G.nsmul_succ, pow_succ, ih]; rfl

  have hcomm : ∀ y z : SchemeHomOver t (projModelStrCR V), G.mul t y z = G.mul t z y :=
    fun y z => LiftIsTorsionAux.mul_comm_specMap 𝒢 h𝒢 h𝒢O B V hΔ ((algebraMap k (DualNumber k)).comp f) y z

  have hQeq : Q = x * Q₀' := by
    show Q = Q * Q₀'⁻¹ * Q₀'
    rw [inv_mul_cancel_right]
  rw [hpow] at hxq hQ₀' ⊢
  rw [hQeq]
  have hxc : x * Q₀' = Q₀' * x := hcomm x Q₀'
  calc (x * Q₀') ^ q = x ^ q * Q₀' ^ q := (Commute.mul_pow hxc q)
    _ = 1 := by rw [hxq, hQ₀']; exact one_mul 1

end S_WeierstrassCurve_DrinfeldGlobal_nsmul_eq_one_of_specMap_fstHom_comp_eq_of_nsmul_eq_one
end P2MW
export P2MW.S_WeierstrassCurve_DrinfeldGlobal_nsmul_eq_one_of_specMap_fstHom_comp_eq_of_nsmul_eq_one (solution)
