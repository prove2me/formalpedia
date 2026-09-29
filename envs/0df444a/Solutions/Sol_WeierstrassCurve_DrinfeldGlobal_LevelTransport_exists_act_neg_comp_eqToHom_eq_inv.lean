-- Prove2me | solution 1 for WeierstrassCurve.DrinfeldGlobal.LevelTransport.exists_act_neg_comp_eqToHom_eq_inv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/07157910-8a41-5012-b5ca-2bdf47c825d9

import Mathlib
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_LevelRelabelling
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Theorems.Thm_WeierstrassProjModel_RelativeGroupLaw_exists_isOriginChartSection_iff_one_eq_kwZeroSect
import Theorems.Thm_WeierstrassProjModel_RelativeGroupLaw_inv_val_eq_comp_negMor_of_one_eq_kwZeroSect
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_DrinfeldGlobal_LevelTransport_exists_act_neg_comp_eqToHom_eq_inv
p2m_attr_erase "simp" "WeierstrassProjModel.kw_lrThird_substHom_X"

set_option autoImplicit false

universe u

p2m_open "CategoryTheory AlgebraicGeometry NeronModelInfra WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal P2MW.S_WeierstrassCurve_DrinfeldGlobal_LevelTransport_exists_act_neg_comp_eqToHom_eq_inv.WeierstrassCurve.DrinfeldGlobal ModularCurve"

attribute [local instance] MvPolynomial.gradedAlgebra WeierstrassProjModel.kw_pbac_awayAlgebra

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "toProjective a₃ a₁ map mk map_id Δ VariableChange variableChange_def Projective"
namespace DrinfeldGlobal
p2m_export "WeierstrassCurve.DrinfeldGlobal" "GroupLaws LevelTransport RawDrinfeldPair cls IsVariableChangeHom"
namespace TransportNeg
p2m_open "WeierstrassCurve.DrinfeldGlobal WeierstrassCurve"

open MvPolynomial

theorem gradedRingHom_ext {T T' : Type u} [CommRing T] [CommRing T'] (W : WeierstrassCurve.Projective T)
    (V : WeierstrassCurve.Projective T') (φ₁ φ₂ : projModelGradingCR W →+*ᵍ projModelGradingCR V)
    (hC : ∀ a : T, φ₁ (cls W (MvPolynomial.C a)) = φ₂ (cls W (MvPolynomial.C a)))
    (hX : ∀ i : Fin 3, φ₁ (cls W (X i)) = φ₂ (cls W (X i))) : φ₁ = φ₂ := by
  have key : φ₁.toRingHom.comp (Ideal.Quotient.mk (projModelHomogeneousIdealCR W).toIdeal) =
      φ₂.toRingHom.comp (Ideal.Quotient.mk (projModelHomogeneousIdealCR W).toIdeal) :=
    MvPolynomial.ringHom_ext (fun a ↦ hC a) (fun i ↦ hX i)
  refine GradedRingHom.ext fun x ↦ ?_
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact RingHom.congr_fun key p

theorem projMap_eq_of_gens {T T' : Type u} [CommRing T] [CommRing T'] (W : WeierstrassCurve.Projective T)
    (gC : T → MvPolynomial (Fin 3) T') (gX : Fin 3 → MvPolynomial (Fin 3) T') :
    ∀ {V₁ V₂ : WeierstrassCurve.Projective T'} (e : V₁ = V₂)
      (φ₁ : projModelGradingCR W →+*ᵍ projModelGradingCR V₁)
      (φ₂ : projModelGradingCR W →+*ᵍ projModelGradingCR V₂)
      (h₁ : HomogeneousIdeal.irrelevant (projModelGradingCR V₁) ≤
        (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ₁)
      (h₂ : HomogeneousIdeal.irrelevant (projModelGradingCR V₂) ≤
        (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ₂),
      (∀ a : T, φ₁ (cls W (MvPolynomial.C a)) = cls V₁ (gC a)) →
      (∀ i : Fin 3, φ₁ (cls W (X i)) = cls V₁ (gX i)) →
      (∀ a : T, φ₂ (cls W (MvPolynomial.C a)) = cls V₂ (gC a)) →
      (∀ i : Fin 3, φ₂ (cls W (X i)) = cls V₂ (gX i)) →
      Proj.map φ₁ h₁ = eqToHom (congrArg projModelCR e) ≫ Proj.map φ₂ h₂ := by
  rintro V₁ _ rfl φ₁ φ₂ h₁ h₂ hC₁ hX₁ hC₂ hX₂
  obtain rfl : φ₁ = φ₂ :=
    gradedRingHom_ext W V₁ φ₁ φ₂ (fun a ↦ (hC₁ a).trans (hC₂ a).symm) (fun i ↦ (hX₁ i).trans (hX₂ i).symm)
  simp

theorem one_val {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (G : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    (G.one t).1 = t ≫ (G.one (𝟙 _)).1 := by
  rw [← G.one_natural (𝟙 _) t t (Category.comp_id t)]
  rfl

theorem negGradedHom_cls {K : Type u} [CommRing K] (W : WeierstrassCurve K) (p : MvPolynomial (Fin 3) K) :
    kw_lrAddNegDiag_negGradedHom W (cls W.toProjective p) = cls W.toProjective (kw_lrAddNegDiag_negSubst W p) :=
  rfl

theorem negMor_comp_negMor {K : Type u} [CommRing K] (W : WeierstrassCurve K) :
    kw_lrAddNegDiag_negMor W ≫ kw_lrAddNegDiag_negMor W = 𝟙 _ := by
  have h : (kw_lrAddNegDiag_negGradedHom W).comp (kw_lrAddNegDiag_negGradedHom W) = GradedRingHom.id _ :=
    GradedRingHom.ext fun x ↦ RingHom.congr_fun (kw_lrAddNegDiag_negGradedHom_comp_self W) x
  have h2 : ∀ (h'), Proj.map ((kw_lrAddNegDiag_negGradedHom W).comp (kw_lrAddNegDiag_negGradedHom W)) h' = 𝟙 _ := by
    rw [h]; intro h'; exact Proj.map_id
  unfold kw_lrAddNegDiag_negMor
  rw [← Proj.map_comp]
  exact h2 _

end WeierstrassCurve.DrinfeldGlobal.TransportNeg

open WeierstrassCurve.DrinfeldGlobal.TransportNeg MvPolynomial in
theorem solution
    {A : Type} [CommRing A] (𝒢 : GroupLaws A) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)
    (q : ℕ) (𝒯 : LevelTransport A 𝒢 q) (h𝒯 : 𝒯.IsSectionTransport)
    (hVC : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve.Projective T) (C : WeierstrassCurve.VariableChange T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (C • W))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (C • W)) ≤ (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
        IsVariableChangeHom W C φ)
    (K : Type) [Field K] [Algebra A K] (x : RawDrinfeldPair K) (hΔ : IsUnit x.curve.Δ) :
    ∃ hc : (𝒯.act ⟨-1, 0, -x.curve.a₁, -x.curve.a₃⟩ x).curve = x.curve,
      (𝒯.act ⟨-1, 0, -x.curve.a₁, -x.curve.a₃⟩ x).P.1 ≫ eqToHom (congrArg projModelCR hc) =
          ((𝒢 K x.curve hΔ).inv (𝟙 _) x.P).1 ∧
        (𝒯.act ⟨-1, 0, -x.curve.a₁, -x.curve.a₃⟩ x).Q.1 ≫ eqToHom (congrArg projModelCR hc) =
          ((𝒢 K x.curve hΔ).inv (𝟙 _) x.Q).1 := by
  obtain ⟨hact, -⟩ := h𝒯
  obtain ⟨hc, hpin⟩ := hact K ⟨-1, 0, -x.curve.a₁, -x.curve.a₃⟩ x

  have e : (⟨-1, 0, -x.curve.a₁, -x.curve.a₃⟩ : WeierstrassCurve.VariableChange K) • x.curve = x.curve := by
    ext <;> simp [WeierstrassCurve.variableChange_def] <;> ring

  obtain ⟨φ, hφ, hvc⟩ := hVC K x.curve ⟨-1, 0, -x.curve.a₁, -x.curve.a₃⟩
  have hgen : ∀ i : Fin 3, φ (cls x.curve (X i)) =
      cls ((⟨-1, 0, -x.curve.a₁, -x.curve.a₃⟩ : WeierstrassCurve.VariableChange K) • x.curve)
        (kw_lrAddNegDiag_negSubstGen x.curve i) := by
    obtain ⟨-, h0, h1, h2⟩ := hvc
    have g0 : φ (cls x.curve (X 0)) =
        cls ((⟨-1, 0, -x.curve.a₁, -x.curve.a₃⟩ : WeierstrassCurve.VariableChange K) • x.curve)
          (kw_lrAddNegDiag_negSubstGen x.curve 0) := by
      rw [h0]; congr 1; simp [kw_lrAddNegDiag_negSubstGen]
    have g1 : φ (cls x.curve (X 1)) =
        cls ((⟨-1, 0, -x.curve.a₁, -x.curve.a₃⟩ : WeierstrassCurve.VariableChange K) • x.curve)
          (kw_lrAddNegDiag_negSubstGen x.curve 1) := by
      rw [h1]; congr 1
      simp [kw_lrAddNegDiag_negSubstGen]
      ring
    have g2 : φ (cls x.curve (X 2)) =
        cls ((⟨-1, 0, -x.curve.a₁, -x.curve.a₃⟩ : WeierstrassCurve.VariableChange K) • x.curve)
          (kw_lrAddNegDiag_negSubstGen x.curve 2) := by
      rw [h2]; congr 1
    intro i
    fin_cases i
    · exact g0
    · exact g1
    · exact g2
  have hν : Proj.map φ hφ = eqToHom (congrArg projModelCR e) ≫ kw_lrAddNegDiag_negMor x.curve := by
    refine projMap_eq_of_gens x.curve (fun a ↦ MvPolynomial.C a) (kw_lrAddNegDiag_negSubstGen x.curve) e φ
      (kw_lrAddNegDiag_negGradedHom x.curve) hφ (kw_lrAddNegDiag_negGradedHom_irrelevant_le x.curve)
      hvc.1 hgen ?_ ?_
    · intro a
      rw [negGradedHom_cls]
      congr 1
      simp [kw_lrAddNegDiag_negSubst]
    · intro i
      rw [negGradedHom_cls]
      congr 1
      simp [kw_lrAddNegDiag_negSubst]

  obtain ⟨hP, hQ⟩ := hpin φ hφ hvc
  rw [hν] at hP hQ

  haveI : WeierstrassCurve.IsElliptic x.curve := ⟨hΔ⟩
  obtain ⟨χ, hχ, hχx, hχz⟩ := h𝒢O K x.curve hΔ
  have hone1 : ((𝒢 K x.curve hΔ).one (𝟙 _)).1 = (kwZeroSect K x.curve).1 :=
    (WeierstrassProjModel.RelativeGroupLaw.exists_isOriginChartSection_iff_one_eq_kwZeroSect x.curve
      (𝒢 K x.curve hΔ)).mp ⟨χ, hχ, hχx, hχz⟩
  have hone : ∀ {S : Scheme.{0}} (t : S ⟶ Spec (CommRingCat.of K)),
      ((𝒢 K x.curve hΔ).one t).1 = t ≫ (kwZeroSect K x.curve).1 := by
    intro S t; rw [one_val, hone1]
  have hinvP := WeierstrassProjModel.RelativeGroupLaw.inv_val_eq_comp_negMor_of_one_eq_kwZeroSect x.curve
    (𝒢 K x.curve hΔ) hone (𝟙 _) x.P
  have hinvQ := WeierstrassProjModel.RelativeGroupLaw.inv_val_eq_comp_negMor_of_one_eq_kwZeroSect x.curve
    (𝒢 K x.curve hΔ) hone (𝟙 _) x.Q
  refine ⟨hc.trans e, ?_, ?_⟩
  · have h := congrArg (· ≫ kw_lrAddNegDiag_negMor x.curve) hP
    simp only [Category.assoc, negMor_comp_negMor, Category.comp_id] at h
    rw [eqToHom_trans] at h
    rw [hinvP]
    exact h
  · have h := congrArg (· ≫ kw_lrAddNegDiag_negMor x.curve) hQ
    simp only [Category.assoc, negMor_comp_negMor, Category.comp_id] at h
    rw [eqToHom_trans] at h
    rw [hinvQ]
    exact h

end S_WeierstrassCurve_DrinfeldGlobal_LevelTransport_exists_act_neg_comp_eqToHom_eq_inv
end P2MW
export P2MW.S_WeierstrassCurve_DrinfeldGlobal_LevelTransport_exists_act_neg_comp_eqToHom_eq_inv (solution)
