-- Prove2me | solution 1 for WeierstrassCurve.DrinfeldGlobal.exists_reducesToOrigin_linComb_iff_eq_zero_of_not_reducesToOrigin
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/7f7c902f-40b7-55ff-ad8c-6b2975652723

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_WeierstrassCurve_FormalGroup
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_ringHom_originChartRing_ext
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_DrinfeldGlobal_exists_reducesToOrigin_linComb_iff_eq_zero_of_not_reducesToOrigin

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal IsLocalRing

attribute [local instance] MvPolynomial.gradedAlgebra

open NeronModelInfra HomogeneousLocalization

noncomputable section

namespace KiiAux

variable {T : Type} [CommRing T] [IsLocalRing T] (W : WeierstrassCurve T) (G : RelativeGroupLaw T (projModelStrCR W))

theorem apply_sc_eq (P : Section W) (χ : OriginChartRing W →+* T)
    (hχ : IsOriginChartSection P χ) (t : T) :
    χ (fromZeroRingHom (projModelGradingCR W) _ (algebraMap T ((projModelGradingCR W) 0) t)) = t := by
  have h := P.2
  rw [hχ] at h
  simp only [projModelStrCR, Category.assoc, Proj.awayι_toSpecZero_assoc, ← Spec.map_comp] at h
  have h2 : Spec.map (CommRingCat.ofHom (algebraMap T ((projModelGradingCR W) 0)) ≫
      CommRingCat.ofHom (fromZeroRingHom (projModelGradingCR W) _) ≫ CommRingCat.ofHom χ) =
      Spec.map (𝟙 _) := by rw [Spec.map_id]; exact h
  have h3 := Spec.map_injective h2
  have h4 := congrArg (fun g : CommRingCat.of T ⟶ CommRingCat.of T ↦ g.hom t) h3
  simpa using h4

def tk (T : Type) [CommRing T] [IsLocalRing T] : Spec (CommRingCat.of (ResidueField T)) ⟶ Spec (CommRingCat.of T) :=
  Spec.map (CommRingCat.ofHom (algebraMap T (ResidueField T)))

theorem tk_def (T : Type) [CommRing T] [IsLocalRing T] :
    tk T = Spec.map (CommRingCat.ofHom (algebraMap T (ResidueField T))) := rfl

theorem tk_comp : tk T ≫ 𝟙 _ = tk T := Category.comp_id _

def red (X : Section W) : SchemeHomOver (tk T) (projModelStrCR W) :=
  schemeHomOverComp (tk T) (tk_comp) X

theorem red_coe (X : Section W) : (red W X).1 = tk T ≫ X.1 := rfl

theorem red_mul (X Y : Section W) :
    red W (G.mul (𝟙 _) X Y) = G.mul (tk T) (red W X) (red W Y) :=
  G.mul_natural (𝟙 _) (tk T) (tk T) tk_comp X Y

theorem red_eq_of_chart (X Y : Section W) (χ χ' : OriginChartRing W →+* T)
    (hX : IsOriginChartSection X χ) (hY : IsOriginChartSection Y χ')
    (h : (algebraMap T (ResidueField T)).comp χ = (algebraMap T (ResidueField T)).comp χ') :
    red W X = red W Y := by
  apply Subtype.ext
  rw [red_coe, red_coe]
  have hX' : X.1 = Spec.map (CommRingCat.ofHom χ) ≫ originChartι W := hX
  have hY' : Y.1 = Spec.map (CommRingCat.ofHom χ') ≫ originChartι W := hY
  rw [hX', hY', ← Category.assoc, ← Category.assoc, tk_def, ← Spec.map_comp, ← Spec.map_comp]
  congr 2
  ext x
  exact congrArg (fun f : OriginChartRing W →+* ResidueField T => f x) h

theorem red_eq_red_one_of_reducesToOrigin
    (χ₀ : OriginChartRing W →+* T) (hχ₀ : IsOriginChartSection (G.one (𝟙 _)) χ₀)
    (hx₀ : χ₀ (xOverY W) = 0) (hz₀ : χ₀ (zOverY W) = 0)
    (X : Section W) (χ : OriginChartRing W →+* T) (hX : ReducesToOrigin X χ (maximalIdeal T)) :
    red W X = red W (G.one (𝟙 _)) := by
  apply red_eq_of_chart W X _ χ χ₀ hX.1 hχ₀
  apply WeierstrassCurve.DrinfeldGlobal.ringHom_originChartRing_ext W
  · intro t
    simp only [RingHom.comp_apply, apply_sc_eq W X χ hX.1, apply_sc_eq W _ χ₀ hχ₀]
  · simp only [RingHom.comp_apply, hx₀, map_zero, IsLocalRing.ResidueField.algebraMap_eq,
      IsLocalRing.residue_eq_zero_iff]
    have := hX.2.1
    simp only [originParam] at this
    exact (Ideal.neg_mem_iff _).mp this
  · simp only [RingHom.comp_apply, hz₀, map_zero, IsLocalRing.ResidueField.algebraMap_eq,
      IsLocalRing.residue_eq_zero_iff]
    have := hX.2.2
    simp only [originW] at this
    exact (Ideal.neg_mem_iff _).mp this

theorem exists_reducesToOrigin_of_red_eq
    (χ₀ : OriginChartRing W →+* T) (hχ₀ : IsOriginChartSection (G.one (𝟙 _)) χ₀)
    (hx₀ : χ₀ (xOverY W) = 0) (hz₀ : χ₀ (zOverY W) = 0)
    (X : Section W) (hred : red W X = red W (G.one (𝟙 _))) :
    ∃ χ : OriginChartRing W →+* T, ReducesToOrigin X χ (maximalIdeal T) := by
  classical
  have hO' : (G.one (𝟙 _)).1 = Spec.map (CommRingCat.ofHom χ₀) ≫ originChartι W := hχ₀
  have hred1 : tk T ≫ X.1 = tk T ≫ (G.one (𝟙 _)).1 := by
    have := congrArg Subtype.val hred
    simpa [red_coe] using this

  haveI : IsLocalHom (CommRingCat.ofHom (algebraMap T (ResidueField T))).hom := by
    rw [CommRingCat.hom_ofHom, IsLocalRing.ResidueField.algebraMap_eq]; infer_instance
  have hcl : (tk T) (closedPoint (ResidueField T)) = closedPoint T := by
    rw [tk_def]; exact Spec_closedPoint
  have hmem : X.1 (closedPoint T) ∈ (originChartι W).opensRange := by
    rw [← hcl, ← Scheme.Hom.comp_apply, hred1, Scheme.Hom.comp_apply, hO', Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩
  have hrange : Set.range X.1 ⊆ Set.range (originChartι W) := by
    rintro _ ⟨x, rfl⟩
    have hs : X.1 x ⤳ X.1 (closedPoint T) :=
      (IsLocalRing.specializes_closedPoint x).map X.1.continuous
    exact hs.mem_open (originChartι W).opensRange.isOpen hmem
  let l := IsOpenImmersion.lift (originChartι W) X.1 hrange
  have hl : l ≫ originChartι W = X.1 := IsOpenImmersion.lift_fac _ _ _
  let χc : CommRingCat.of (OriginChartRing W) ⟶ CommRingCat.of T := (Scheme.Spec.preimage l).unop
  have hχc : Spec.map χc = l := by
    show Scheme.Spec.map (Scheme.Spec.preimage l).unop.op = l
    rw [Quiver.Hom.op_unop, Scheme.Spec.map_preimage]
  refine ⟨χc.hom, ?_, ?_, ?_⟩
  · show X.1 = Spec.map (CommRingCat.ofHom χc.hom) ≫ originChartι W
    rw [CommRingCat.ofHom_hom, hχc, hl]
  all_goals
    have hcomp : tk T ≫ Spec.map χc = tk T ≫ Spec.map (CommRingCat.ofHom χ₀) := by
      rw [← cancel_mono (originChartι W), Category.assoc, Category.assoc, hχc, hl, ← hO', hred1]
    rw [tk_def, ← Spec.map_comp, ← Spec.map_comp] at hcomp
    have hc := Spec.map_injective hcomp
  · have h4 := congrArg (fun g : CommRingCat.of (OriginChartRing W) ⟶ CommRingCat.of (ResidueField T) ↦
      g.hom (xOverY W)) hc
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply, hx₀, map_zero,
      IsLocalRing.ResidueField.algebraMap_eq, IsLocalRing.residue_eq_zero_iff] at h4
    simpa [originParam] using h4
  · have h4 := congrArg (fun g : CommRingCat.of (OriginChartRing W) ⟶ CommRingCat.of (ResidueField T) ↦
      g.hom (zOverY W)) hc
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply, hz₀, map_zero,
      IsLocalRing.ResidueField.algebraMap_eq, IsLocalRing.residue_eq_zero_iff] at h4
    simpa [originW] using h4

end KiiAux

end

theorem solution
    {T : Type} [CommRing T] [IsLocalRing T] [IsNoetherianRing T] [IsAdicComplete (maximalIdeal T) T]
    (W : WeierstrassCurve T) [W.IsElliptic]
    (G : RelativeGroupLaw T (projModelStrCR W))
    (hGpts : ∃ ev, IsPointsEval W G ev)
    (hGone : ∃ χ : OriginChartRing W →+* T,
      IsOriginChartSection (G.one (𝟙 _)) χ ∧ χ (xOverY W) = 0 ∧ χ (zOverY W) = 0)
    (q : ℕ) [Fact q.Prime]
    (P Q : Section W) (χP : OriginChartRing W →+* T) (hP : ReducesToOrigin P χP (maximalIdeal T))
    (hQq : G.nsmul (𝟙 _) q Q = G.one (𝟙 _))
    (hQ : ∀ χ : OriginChartRing W →+* T, ¬ ReducesToOrigin Q χ (maximalIdeal T))
    (a b : ℕ) (hb : b < q) :
    (∃ χ : OriginChartRing W →+* T, ReducesToOrigin (linComb G P Q a b) χ (maximalIdeal T)) ↔ b = 0 := by
  classical
  obtain ⟨ev, hev⟩ := hGpts
  obtain ⟨χ₀, hχ₀, hx₀, hz₀⟩ := hGone
  haveI : DecidableEq (ResidueField T) := Classical.decEq _

  let e : Section W → ((W : WeierstrassCurve.Projective T).baseChange (ResidueField T)).toAffine.Point :=
    fun X => ev (ResidueField T) (KiiAux.red W X)
  have e_mul : ∀ X Y : Section W, e (G.mul (𝟙 _) X Y) = e X + e Y := by
    intro X Y
    show ev _ (KiiAux.red W (G.mul (𝟙 _) X Y)) = _
    rw [KiiAux.red_mul W G]
    exact hev.1 (ResidueField T) _ _
  have e_one : e (G.one (𝟙 _)) = 0 := by
    have h := e_mul (G.one (𝟙 _)) (G.one (𝟙 _))
    rw [G.one_mul] at h
    simpa using h
  have e_nsmul : ∀ (n : ℕ) (X : Section W), e (G.nsmul (𝟙 _) n X) = n • e X := by
    intro n X
    induction n with
    | zero => simp [RelativeGroupLaw.nsmul_zero, e_one]
    | succ n ih => rw [RelativeGroupLaw.nsmul_succ, e_mul, ih, succ_nsmul]
  have e_red0 : ∀ (X : Section W) (χ : OriginChartRing W →+* T),
      ReducesToOrigin X χ (maximalIdeal T) → e X = 0 := by
    intro X χ hX
    show ev _ (KiiAux.red W X) = 0
    rw [KiiAux.red_eq_red_one_of_reducesToOrigin W G χ₀ hχ₀ hx₀ hz₀ X χ hX]
    exact e_one
  have red0_of_e : ∀ X : Section W, e X = 0 → ∃ χ : OriginChartRing W →+* T, ReducesToOrigin X χ (maximalIdeal T) := by
    intro X hX
    apply KiiAux.exists_reducesToOrigin_of_red_eq W G χ₀ hχ₀ hx₀ hz₀ X
    apply (ev (ResidueField T)).injective
    change e X = e (G.one (𝟙 _))
    rw [hX, e_one]
  have eP : e P = 0 := e_red0 P χP hP
  have e_lin : e (linComb G P Q a b) = b • e Q := by
    show e (G.mul _ (G.nsmul _ a P) (G.nsmul _ b Q)) = _
    rw [e_mul, e_nsmul, e_nsmul, eP, nsmul_zero, zero_add]
  constructor
  · rintro ⟨χ, hχ⟩
    have h0 : b • e Q = 0 := by rw [← e_lin]; exact e_red0 _ χ hχ
    have hQ0 : e Q ≠ 0 := fun h => (red0_of_e Q h).elim fun χ' hχ' => hQ χ' hχ'
    have hqQ : q • e Q = 0 := by rw [← e_nsmul, hQq, e_one]
    have hord : addOrderOf (e Q) = q := (addOrderOf_eq_prime_iff.mpr ⟨hqQ, hQ0⟩)
    have hdvd : q ∣ b := by rw [← hord]; exact addOrderOf_dvd_iff_nsmul_eq_zero.mpr h0
    exact Nat.eq_zero_of_dvd_of_lt hdvd hb
  · rintro rfl
    apply red0_of_e
    rw [e_lin, zero_nsmul]

end S_WeierstrassCurve_DrinfeldGlobal_exists_reducesToOrigin_linComb_iff_eq_zero_of_not_reducesToOrigin
end P2MW
export P2MW.S_WeierstrassCurve_DrinfeldGlobal_exists_reducesToOrigin_linComb_iff_eq_zero_of_not_reducesToOrigin (solution)
