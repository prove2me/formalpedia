-- Prove2me | solution 1 for WeierstrassProjModel.exists_relativeGroupLaw_isCommutative_one_eq_zeroSect_of_isElliptic_of_baseChangeIso
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/b5e78be1-8f73-53c4-ac33-e4f58119d974

import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Theorems.Thm_WeierstrassProjModel_relativeGroupLaw_nonempty_of_isElliptic_of_baseChangeIso_of_isNoetherianRing
import Theorems.Thm_WeierstrassProjModel_RelativeGroupLaw_mul_comm_at_field_of_isElliptic_of_baseChangeIso
import Theorems.Thm_WeierstrassProjModel_projModel_pullback_iso_baseChange
import Theorems.Thm_WeierstrassProjModel_projModelStrCR_smoothOfRelativeDimension_one
import Theorems.Thm_AlgebraicGeometry_Smooth_isReduced_of_isReduced_of_isLocallyNoetherian
import Theorems.Thm_WeierstrassProjModel_projModel_isPullback_baseChange_ring
import Theorems.Thm_WeierstrassProjModel_RelativeGroupLaw_exists_isCommutative_one_eq_zeroSect_of_isCommutative
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.AlgebraicGeometry.EllipticCurve.ModelsWithJ
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.AlgebraicGeometry.Noetherian
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassProjModel_exists_relativeGroupLaw_isCommutative_one_eq_zeroSect_of_isElliptic_of_baseChangeIso
p2m_attr_erase "simp" "WeierstrassProjModel.kw_lrThird_substHom_X GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left"

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel

universe u

noncomputable section

namespace P2mGroupLawComm

section BaseChange

variable {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
variable {R₀ : Type u} [CommRing R₀] (φ : R₀ →+* R)
variable {A₀ : Scheme.{u}} {f₀ : A₀ ⟶ Spec (CommRingCat.of R₀)} {g : A ⟶ A₀}

local notation "sφ" => Spec.map (CommRingCat.ofHom φ)

def pushPoint (hsq : g ≫ f₀ = f ≫ sφ) {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    (x : SchemeHomOver t f) : SchemeHomOver (t ≫ sφ) f₀ :=
  ⟨x.1 ≫ g, by rw [Category.assoc, hsq, ← Category.assoc, x.2]⟩

@[scoped simp]
theorem pushPoint_coe (hsq : g ≫ f₀ = f ≫ sφ) {T : Scheme.{u}}
    {t : T ⟶ Spec (CommRingCat.of R)} (x : SchemeHomOver t f) :
    (pushPoint φ hsq x).1 = x.1 ≫ g :=
  rfl

def pullPoint (H : IsPullback g f f₀ sφ) {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    (y : SchemeHomOver (t ≫ sφ) f₀) : SchemeHomOver t f :=
  ⟨H.lift y.1 t y.2, H.lift_snd _ _ _⟩

@[scoped simp]
theorem pullPoint_coe_fst (H : IsPullback g f f₀ sφ) {T : Scheme.{u}}
    {t : T ⟶ Spec (CommRingCat.of R)} (y : SchemeHomOver (t ≫ sφ) f₀) :
    (pullPoint φ H y).1 ≫ g = y.1 :=
  H.lift_fst _ _ _

@[scoped simp]
theorem pullPoint_coe_snd (H : IsPullback g f f₀ sφ) {T : Scheme.{u}}
    {t : T ⟶ Spec (CommRingCat.of R)} (y : SchemeHomOver (t ≫ sφ) f₀) :
    (pullPoint φ H y).1 ≫ f = t :=
  H.lift_snd _ _ _

def pointEquiv (H : IsPullback g f f₀ sφ) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    SchemeHomOver t f ≃ SchemeHomOver (t ≫ sφ) f₀ where
  toFun := pushPoint φ H.w
  invFun := pullPoint φ H
  left_inv x := Subtype.ext (H.hom_ext (by simp) (by simp [x.2]))
  right_inv y := Subtype.ext (H.lift_fst _ _ _)

@[scoped simp]
theorem pointEquiv_apply_coe (H : IsPullback g f f₀ sφ) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f) :
    (pointEquiv φ H t x).1 = x.1 ≫ g :=
  rfl

theorem pointEquiv_natural (H : IsPullback g f f₀ sφ) {T T' : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (t' : T' ⟶ Spec (CommRingCat.of R))
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x : SchemeHomOver t f) :
    pointEquiv φ H t' (schemeHomOverComp ψ hψ x) =
      schemeHomOverComp ψ (by rw [← Category.assoc, hψ]) (pointEquiv φ H t x) :=
  Subtype.ext (by simp)

private def _root_.P2mGroupLawComm.baseChange (G₀ : RelativeGroupLaw R₀ f₀) (H : IsPullback g f f₀ sφ) :
    RelativeGroupLaw R f where
  mul t x y := (pointEquiv φ H t).symm (G₀.mul _ (pointEquiv φ H t x) (pointEquiv φ H t y))
  one t := (pointEquiv φ H t).symm (G₀.one _)
  inv t x := (pointEquiv φ H t).symm (G₀.inv _ (pointEquiv φ H t x))
  mul_assoc t x y z := by simp only [Equiv.apply_symm_apply, G₀.mul_assoc]
  one_mul t x := by simp only [Equiv.apply_symm_apply, G₀.one_mul, Equiv.symm_apply_apply]
  mul_one t x := by simp only [Equiv.apply_symm_apply, G₀.mul_one, Equiv.symm_apply_apply]
  inv_mul_cancel t x := by simp only [Equiv.apply_symm_apply, G₀.inv_mul_cancel]
  mul_natural t t' ψ hψ x y := by
    apply (pointEquiv φ H t').injective
    rw [pointEquiv_natural, Equiv.apply_symm_apply, Equiv.apply_symm_apply,
      G₀.mul_natural (t ≫ sφ) (t' ≫ sφ) ψ (by rw [← Category.assoc, hψ]),
      ← pointEquiv_natural, ← pointEquiv_natural]

p2m_export "P2mGroupLawComm" "baseChange"
theorem baseChange_mul_push (G₀ : RelativeGroupLaw R₀ f₀) (H : IsPullback g f f₀ sφ)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f) :
    pointEquiv φ H t ((baseChange φ G₀ H).mul t x y) =
      G₀.mul _ (pointEquiv φ H t x) (pointEquiv φ H t y) :=
  Equiv.apply_symm_apply _ _

theorem baseChange_comm (G₀ : RelativeGroupLaw R₀ f₀) (H : IsPullback g f f₀ sφ)
    (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R₀))
      (x y : SchemeHomOver t f₀), G₀.mul t x y = G₀.mul t y x)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f) :
    (baseChange φ G₀ H).mul t x y = (baseChange φ G₀ H).mul t y x := by
  apply (pointEquiv φ H t).injective
  rw [baseChange_mul_push, baseChange_mul_push, hcomm]

end BaseChange

namespace Universal

abbrev Poly : Type u := MvPolynomial (ULift.{u} (Fin 5)) ℤ

def curve : WeierstrassCurve Poly.{u} :=
  ⟨MvPolynomial.X ⟨0⟩, MvPolynomial.X ⟨1⟩, MvPolynomial.X ⟨2⟩, MvPolynomial.X ⟨3⟩,
    MvPolynomial.X ⟨4⟩⟩

abbrev Ring : Type u := Localization.Away (curve.{u}).Δ

def ellCurve : WeierstrassCurve Ring.{u} := curve.map (algebraMap Poly.{u} Ring.{u})

scoped instance ellCurve_isElliptic : (ellCurve.{u}).IsElliptic :=
  ⟨by rw [ellCurve, WeierstrassCurve.map_Δ]; exact IsLocalization.Away.algebraMap_isUnit _⟩

universe v

variable {S : Type v} [CommRing S]

def coeff (V : WeierstrassCurve S) : ULift.{u} (Fin 5) → S :=
  fun i => ![V.a₁, V.a₂, V.a₃, V.a₄, V.a₆] i.down

def evalAt (V : WeierstrassCurve S) : Poly.{u} →+* S :=
  MvPolynomial.eval₂Hom (Int.castRingHom S) (coeff V)

@[scoped simp] theorem evalAt_X (V : WeierstrassCurve S) (i : Fin 5) :
    evalAt V (MvPolynomial.X ⟨i⟩) = ![V.a₁, V.a₂, V.a₃, V.a₄, V.a₆] i := by
  simp [evalAt, coeff]

theorem curve_map_evalAt (V : WeierstrassCurve S) : curve.{u}.map (evalAt V) = V := by
  ext <;> simp [curve]

theorem evalAt_Δ (V : WeierstrassCurve S) : evalAt V curve.{u}.Δ = V.Δ := by
  rw [← WeierstrassCurve.map_Δ, curve_map_evalAt]

theorem curve_Δ_ne_zero : curve.{u}.Δ ≠ 0 := by
  intro h
  have h64 := evalAt_Δ.{u} (WeierstrassCurve.ofJ1728 ℤ)
  rw [h, map_zero, WeierstrassCurve.ofJ1728_Δ] at h64
  norm_num at h64

scoped instance : IsDomain Ring.{u} :=
  IsLocalization.isDomain_localization
    (powers_le_nonZeroDivisors_of_noZeroDivisors curve_Δ_ne_zero)

scoped instance : IsNoetherianRing Ring.{u} := inferInstance

def classify (V : WeierstrassCurve S) [V.IsElliptic] : Ring.{u} →+* S :=
  IsLocalization.Away.lift curve.{u}.Δ (g := evalAt V)
    (by rw [evalAt_Δ]; exact V.isUnit_Δ)

theorem classify_comp_algebraMap (V : WeierstrassCurve S) [V.IsElliptic] :
    (classify V).comp (algebraMap Poly.{u} Ring.{u}) = evalAt V :=
  IsLocalization.Away.lift_comp _ _

theorem ellCurve_map_classify (V : WeierstrassCurve S) [V.IsElliptic] :
    ellCurve.{u}.map (classify V) = V := by
  rw [ellCurve, WeierstrassCurve.map_map, classify_comp_algebraMap, curve_map_evalAt]

end Universal
p2m_reactivate "P2MW.S_WeierstrassProjModel_exists_relativeGroupLaw_isCommutative_one_eq_zeroSect_of_isElliptic_of_baseChangeIso.P2mGroupLawComm.Universal"

section Rigidity

variable {R : Type u} [CommRing R]

scoped instance isSeparated_projModelStrCR (V : WeierstrassCurve.Projective R) :
    IsSeparated (projModelStrCR V) := by
  unfold projModelStrCR; infer_instance

theorem mul_comm_of_universalPair {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (G : RelativeGroupLaw R f)
    (huniv : G.mul (pullback.fst f f ≫ f) ⟨pullback.fst f f, rfl⟩ ⟨pullback.snd f f, pullback.condition.symm⟩ =
      G.mul (pullback.fst f f ≫ f) ⟨pullback.snd f f, pullback.condition.symm⟩ ⟨pullback.fst f f, rfl⟩)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f) :
    G.mul t x y = G.mul t y x := by
  set p₁ : SchemeHomOver (pullback.fst f f ≫ f) f := ⟨pullback.fst f f, rfl⟩
  set p₂ : SchemeHomOver (pullback.fst f f ≫ f) f := ⟨pullback.snd f f, pullback.condition.symm⟩
  let ψ : T ⟶ pullback f f := pullback.lift x.1 y.1 (by rw [x.2, y.2])
  have hψ : ψ ≫ (pullback.fst f f ≫ f) = t := by
    rw [← Category.assoc, pullback.lift_fst, x.2]
  have hx : schemeHomOverComp ψ hψ p₁ = x := Subtype.ext (pullback.lift_fst _ _ _)
  have hy : schemeHomOverComp ψ hψ p₂ = y := Subtype.ext (pullback.lift_snd _ _ _)
  have h₁ := G.mul_natural _ t ψ hψ p₁ p₂
  have h₂ := G.mul_natural _ t ψ hψ p₂ p₁
  rw [hx, hy] at h₁ h₂
  rw [← h₁, ← h₂, huniv]

theorem mul_comm_at_specField (V : WeierstrassCurve.Projective R) [V.toAffine.IsElliptic]
    (hbc : ∀ (K : Type u) [Field K] [Algebra R K],
        Nonempty (pullback (projModelStrCR V)
            (Spec.map (CommRingCat.ofHom (algebraMap R K)))
          ≅ projModelCR (V.baseChange K)))
    (G : RelativeGroupLaw R (projModelStrCR V))
    (K : Type u) [Field K] (q : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R))
    (P Q : SchemeHomOver q (projModelStrCR V)) :
    G.mul q P Q = G.mul q Q P := by
  letI : Algebra R K := (Spec.preimage q).hom.toAlgebra
  have hq : q = Spec.map (CommRingCat.ofHom (algebraMap R K)) := by
    rw [RingHom.algebraMap_toAlgebra, CommRingCat.ofHom_hom, Spec.map_preimage]
  clear_value ‹Algebra R K›
  subst hq
  exact RelativeGroupLaw.mul_comm_at_field_of_isElliptic_of_baseChangeIso V hbc G K P Q

theorem mul_comm_of_isReduced [IsReduced R] [IsNoetherianRing R]
    (V : WeierstrassCurve.Projective R) [V.toAffine.IsElliptic]
    (hbc : ∀ (K : Type u) [Field K] [Algebra R K],
        Nonempty (pullback (projModelStrCR V)
            (Spec.map (CommRingCat.ofHom (algebraMap R K)))
          ≅ projModelCR (V.baseChange K)))
    (G : RelativeGroupLaw R (projModelStrCR V))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t (projModelStrCR V)) :
    G.mul t x y = G.mul t y x := by
  haveI : V.IsElliptic := ‹V.toAffine.IsElliptic›

  haveI : SmoothOfRelativeDimension 1 (projModelStrCR V) := projModelStrCR_smoothOfRelativeDimension_one V
  haveI : Smooth (projModelStrCR V) := SmoothOfRelativeDimension.smooth 1 (projModelStrCR V)
  haveI : _root_.IsReduced (CommRingCat.of R) := ‹IsReduced R›
  haveI : IsNoetherianRing (CommRingCat.of R) := ‹IsNoetherianRing R›
  haveI : IsReduced (pullback (projModelStrCR V) (projModelStrCR V)) :=
    Smooth.isReduced_of_isReduced_of_isLocallyNoetherian
      (pullback.fst (projModelStrCR V) (projModelStrCR V) ≫ projModelStrCR V)
  apply mul_comm_of_universalPair
  apply Subtype.ext
  refine ext_of_fromSpecResidueField_eq _ _ (projModelStrCR V) Set.univ dense_univ (fun z _ => ?_) ?_
  ·
    have e₁ := congrArg Subtype.val (G.mul_natural
      (pullback.fst (projModelStrCR V) (projModelStrCR V) ≫ projModelStrCR V) _
      ((pullback (projModelStrCR V) (projModelStrCR V)).fromSpecResidueField z) rfl
      ⟨pullback.fst (projModelStrCR V) (projModelStrCR V), rfl⟩
      ⟨pullback.snd (projModelStrCR V) (projModelStrCR V), pullback.condition.symm⟩)
    have e₂ := congrArg Subtype.val (G.mul_natural
      (pullback.fst (projModelStrCR V) (projModelStrCR V) ≫ projModelStrCR V) _
      ((pullback (projModelStrCR V) (projModelStrCR V)).fromSpecResidueField z) rfl
      ⟨pullback.snd (projModelStrCR V) (projModelStrCR V), pullback.condition.symm⟩
      ⟨pullback.fst (projModelStrCR V) (projModelStrCR V), rfl⟩)
    simp only [schemeHomOverComp_coe] at e₁ e₂
    rw [e₁, e₂]
    exact congrArg Subtype.val (mul_comm_at_specField V hbc G _ _ _ _)
  · exact ((G.mul _ _ _).2).trans ((G.mul _ _ _).2).symm

end Rigidity
p2m_reactivate "P2MW.S_WeierstrassProjModel_exists_relativeGroupLaw_isCommutative_one_eq_zeroSect_of_isElliptic_of_baseChangeIso.P2mGroupLawComm.Universal"

theorem main {R : Type u} [CommRing R] (V : WeierstrassCurve.Projective R)
    [V.toAffine.IsElliptic] :
    ∃ G₀ : RelativeGroupLaw R (projModelStrCR V),
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t (projModelStrCR V)),
          G₀.mul t x y = G₀.mul t y x)
      ∧ (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)),
          (G₀.one t).1 = t ≫ (kwZeroSect R V.toAffine).1) := by
  haveI : V.IsElliptic := ‹V.toAffine.IsElliptic›

  let U : Type u := Universal.Ring.{u}
  let E : WeierstrassCurve.Projective U := Universal.ellCurve.{u}
  haveI hE : E.toAffine.IsElliptic := Universal.ellCurve_isElliptic
  have hbcE := projModel_pullback_iso_baseChange E
  obtain ⟨GE⟩ := relativeGroupLaw_nonempty_of_isElliptic_of_baseChangeIso_of_isNoetherianRing E hbcE

  have hcommE : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of U))
      (x y : SchemeHomOver t (projModelStrCR E)), GE.mul t x y = GE.mul t y x :=
    fun t x y => mul_comm_of_isReduced E hbcE GE t x y

  let φ : U →+* R := Universal.classify (V : WeierstrassCurve R)
  letI : Algebra U R := φ.toAlgebra
  obtain ⟨α, hα⟩ := projModel_isPullback_baseChange_ring E R
  let G₁ : RelativeGroupLaw R (projModelStrCR (E.baseChange R)) := baseChange (algebraMap U R) GE hα
  have hcomm₁ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
      (x y : SchemeHomOver t (projModelStrCR (E.baseChange R))), G₁.mul t x y = G₁.mul t y x :=
    fun t x y => baseChange_comm (algebraMap U R) GE hα (fun t x y => hcommE t x y) t x y

  have h₂ := RelativeGroupLaw.exists_isCommutative_one_eq_zeroSect_of_isCommutative
    (E.baseChange R) G₁ (fun t x y => hcomm₁ t x y)

  have hV : E.baseChange R = V := by
    change Universal.ellCurve.map (algebraMap U R) = V
    exact Universal.ellCurve_map_classify (V : WeierstrassCurve R)
  exact hV ▸ h₂

end P2mGroupLawComm
p2m_reactivate "P2MW.S_WeierstrassProjModel_exists_relativeGroupLaw_isCommutative_one_eq_zeroSect_of_isElliptic_of_baseChangeIso.P2mGroupLawComm.Universal P2MW.S_WeierstrassProjModel_exists_relativeGroupLaw_isCommutative_one_eq_zeroSect_of_isElliptic_of_baseChangeIso.P2mGroupLawComm"

end
p2m_reactivate "P2MW.S_WeierstrassProjModel_exists_relativeGroupLaw_isCommutative_one_eq_zeroSect_of_isElliptic_of_baseChangeIso.P2mGroupLawComm.Universal P2MW.S_WeierstrassProjModel_exists_relativeGroupLaw_isCommutative_one_eq_zeroSect_of_isElliptic_of_baseChangeIso.P2mGroupLawComm"

theorem solution
    {R : Type u} [CommRing R] (V : WeierstrassCurve.Projective R)
    [V.toAffine.IsElliptic]
    (hbc : ∀ (K : Type u) [Field K] [Algebra R K],
        Nonempty (pullback (projModelStrCR V)
            (Spec.map (CommRingCat.ofHom (algebraMap R K)))
          ≅ projModelCR (V.baseChange K))) :
    ∃ G₀ : RelativeGroupLaw R (projModelStrCR V),
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t (projModelStrCR V)),
          G₀.mul t x y = G₀.mul t y x)
      ∧ (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)),
          (G₀.one t).1 = t ≫ (kwZeroSect R V.toAffine).1) :=
  P2mGroupLawComm.main V

end S_WeierstrassProjModel_exists_relativeGroupLaw_isCommutative_one_eq_zeroSect_of_isElliptic_of_baseChangeIso
end P2MW
export P2MW.S_WeierstrassProjModel_exists_relativeGroupLaw_isCommutative_one_eq_zeroSect_of_isElliptic_of_baseChangeIso (solution)
