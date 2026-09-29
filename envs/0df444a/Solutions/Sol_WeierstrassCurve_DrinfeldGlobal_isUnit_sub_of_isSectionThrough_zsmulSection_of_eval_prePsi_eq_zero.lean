-- Prove2me | solution 1 for WeierstrassCurve.DrinfeldGlobal.isUnit_sub_of_isSectionThrough_zsmulSection_of_eval_prePsi_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/9612f024-fd12-5dc4-a603-224d303a235e

import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_PointChart
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_LevelRelabelling
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_exists_groupLaws_levelTransport_isChordTangent_isOriginIdentity_isSectionTransport
import Theorems.Thm_WeierstrassProjModel_RelativeGroupLaw_mul_eq_of_one_eq_of_isElliptic
import Theorems.Thm_WeierstrassProjModel_RelativeGroupLaw_exists_isOriginChartSection_iff_one_eq_kwZeroSect
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_LevelTransport_map_relabel_eq_relabel_map
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_isSectionThrough_map_of_isSectionTransport
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_isSectionThrough_zlinComb_of_isSectionThrough
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_equation_iff_exists_isSectionThrough_and_eq_iff_of_isSectionThrough
import Theorems.Thm_WeierstrassCurve_Affine_Point_nsmul_some_eq_zero_iff_eval_prePsi
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_DrinfeldGlobal_isUnit_sub_of_isSectionThrough_zsmulSection_of_eval_prePsi_eq_zero
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "WeierstrassProjModel.kw_lrThird_substHom_X compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

open AlgebraicGeometry CategoryTheory WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal ModularCurve.LevelRelabelling
open scoped Classical

attribute [local instance] MvPolynomial.gradedAlgebra

namespace LBAux

theorem zlinComb_eq_of_one_eq {T : Type} [CommRing T] (W : WeierstrassCurve.Projective T) [W.toAffine.IsElliptic]
    (G₀ G₁ : RelativeGroupLaw T (projModelStrCR W))
    (h1 : (G₀.one (𝟙 _)).1 = (G₁.one (𝟙 _)).1) (P Q : Section W) (a b : ℤ) :
    zlinComb G₀ P Q a b = zlinComb G₁ P Q a b := by
  have hmul : ∀ x y : Section W, G₀.mul (𝟙 _) x y = G₁.mul (𝟙 _) x y :=
    fun x y => RelativeGroupLaw.mul_eq_of_one_eq_of_isElliptic W G₀ G₁ h1 (𝟙 _) x y
  have hone : G₀.one (𝟙 (base (T := T))) = G₁.one (𝟙 _) := Subtype.ext h1
  have hnsmul : ∀ (n : ℕ) (x : Section W), G₀.nsmul (𝟙 _) n x = G₁.nsmul (𝟙 _) n x := by
    intro n x
    induction n with
    | zero => exact hone
    | succ n ih => rw [G₀.nsmul_succ, G₁.nsmul_succ, ih, hmul]
  have hinv : ∀ x : Section W, G₀.inv (𝟙 _) x = G₁.inv (𝟙 _) x := by
    intro x
    letI := G₁.pointGroup (𝟙 (base (T := T)))
    have h : G₀.inv (𝟙 _) x * x = 1 := by
      show G₁.mul (𝟙 _) (G₀.inv (𝟙 _) x) x = G₁.one (𝟙 _)
      rw [← hmul, G₀.inv_mul_cancel, hone]
    exact eq_inv_of_mul_eq_one_left h
  have hz : ∀ (n : ℤ) (x : Section W), zsmulSection G₀ n x = zsmulSection G₁ n x := by
    intro n x
    cases n with
    | ofNat k => exact hnsmul k x
    | negSucc k =>
      show G₀.inv _ (G₀.nsmul _ (k + 1) x) = G₁.inv _ (G₁.nsmul _ (k + 1) x)
      rw [hnsmul, hinv]
  show G₀.mul _ (zsmulSection G₀ a P) (zsmulSection G₀ b Q) = G₁.mul _ (zsmulSection G₁ a P) (zsmulSection G₁ b Q)
  rw [hz, hz, hmul]

theorem zlinComb_self_zero {T : Type} [CommRing T] {W : WeierstrassCurve.Projective T} (G : RelativeGroupLaw T (projModelStrCR W))
    (S : Section W) (a : ℤ) : zlinComb G S S a 0 = zsmulSection G a S := by
  letI := G.pointGroup (𝟙 _)
  show G.mul _ (zsmulSection G a S) (zsmulSection G 0 S) = zsmulSection G a S
  have h0 : zsmulSection G 0 S = G.one (𝟙 _) := rfl
  rw [h0]
  exact mul_one (zsmulSection G a S)

theorem zlinComb_one_zero {T : Type} [CommRing T] {W : WeierstrassCurve.Projective T}
    (G : RelativeGroupLaw T (projModelStrCR W)) (P Q : Section W) : zlinComb G P Q 1 0 = P := by
  show G.mul _ (G.nsmul _ 1 P) (G.nsmul _ 0 Q) = P
  rw [G.nsmul_one_apply, G.nsmul_zero, G.mul_one]

section FieldCase

variable {F : Type} [Field F]

theorem exists_zsmul_eq_some (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ)
    (W : WeierstrassCurve F) (hΔ : IsUnit W.Δ) (x y : F) (hxy : W.toAffine.Equation x y) (hx : (W.preΨ ℓ).eval x = 0)
    (a : ℤ) (ha : ¬ ((ℓ : ℤ) ∣ a)) :
    ∃ (u v : F) (huv : W.toAffine.Nonsingular u v),
      a • toPoint W x y + (0 : ℤ) • toPoint W x y = WeierstrassCurve.Affine.Point.some u v huv := by
  have hp : ℓ.Prime := Fact.out
  haveI : NeZero ℓ := ⟨hp.ne_zero⟩
  have hℓ2 : ℓ ≠ 2 := by omega
  have hodd : Odd ℓ := hp.odd_of_ne_two hℓ2
  haveI : W.IsElliptic := ⟨hΔ⟩
  have nP := W.toAffine.equation_iff_nonsingular.mp hxy
  set P : W.toAffine.Point := WeierstrassCurve.Affine.Point.some _ _ nP with hPdef
  have hℓP : (ℓ : ℤ) • P = 0 := by
    rw [natCast_zsmul, hPdef]
    refine (WeierstrassCurve.Affine.Point.nsmul_some_eq_zero_iff_eval_prePsi W hodd nP).mpr ?_
    rw [← WeierstrassCurve.preΨ_ofNat]; exact hx
  have hP0 : P ≠ 0 := WeierstrassCurve.Affine.Point.some_ne_zero _
  have haP : a • P ≠ 0 := by
    intro hm
    apply ha
    by_contra hdvd
    have hcopN : Nat.Coprime ℓ a.natAbs :=
      (Nat.Prime.coprime_iff_not_dvd hp).mpr (fun h0 => hdvd (Int.natCast_dvd.mpr h0))
    have hcop : IsCoprime (ℓ : ℤ) a := by
      rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_eq_natAbs, Int.natAbs_natCast]; exact hcopN
    obtain ⟨u, v, huv⟩ := hcop
    apply hP0
    calc P = (1 : ℤ) • P := (one_zsmul P).symm
      _ = (u * ℓ + v * a) • P := by rw [huv]
      _ = u • ((ℓ : ℤ) • P) + v • (a • P) := by rw [add_zsmul, mul_zsmul, mul_zsmul]
      _ = 0 := by rw [hℓP, hm, zsmul_zero, zsmul_zero, add_zero]
  have htoP : toPoint W x y = P := dif_pos nP
  rw [htoP, zero_zsmul, add_zero]
  cases hQ : a • P with
  | zero => exact absurd hQ haP
  | some u v huv => exact ⟨u, v, huv, rfl⟩

end FieldCase

section FieldCase2

variable {F : Type} [Field F]

theorem fst_ne_of_zsmul_eq_some (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ)
    (W : WeierstrassCurve F) (hΔ : IsUnit W.Δ) (x y : F) (hxy : W.toAffine.Equation x y) (hx : (W.preΨ ℓ).eval x = 0)
    (a : ℤ) (ha₁ : ¬ ((ℓ : ℤ) ∣ a - 1)) (ha₂ : ¬ ((ℓ : ℤ) ∣ a + 1))
    (u v : F) (huv : W.toAffine.Nonsingular u v)
    (e : a • toPoint W x y + (0 : ℤ) • toPoint W x y = WeierstrassCurve.Affine.Point.some u v huv) :
    u ≠ x := by
  have hp : ℓ.Prime := Fact.out
  haveI : NeZero ℓ := ⟨hp.ne_zero⟩
  have hℓ2 : ℓ ≠ 2 := by omega
  have hodd : Odd ℓ := hp.odd_of_ne_two hℓ2
  haveI : W.IsElliptic := ⟨hΔ⟩
  have nP := W.toAffine.equation_iff_nonsingular.mp hxy
  have hℓP : (ℓ : ℤ) • WeierstrassCurve.Affine.Point.some x y nP = 0 := by
    rw [natCast_zsmul]
    refine (WeierstrassCurve.Affine.Point.nsmul_some_eq_zero_iff_eval_prePsi W hodd nP).mpr ?_
    rw [← WeierstrassCurve.preΨ_ofNat]; exact hx
  have hP0 : WeierstrassCurve.Affine.Point.some x y nP ≠ 0 := WeierstrassCurve.Affine.Point.some_ne_zero _
  have hordP : addOrderOf (WeierstrassCurve.Affine.Point.some x y nP) = ℓ := by
    refine addOrderOf_eq_prime_iff.mpr ⟨?_, hP0⟩
    have h := hℓP
    rwa [natCast_zsmul] at h
  have key : ∀ b : ℤ, b • WeierstrassCurve.Affine.Point.some x y nP = 0 → (ℓ : ℤ) ∣ b := by
    intro b hb
    have h := addOrderOf_dvd_iff_zsmul_eq_zero.mpr hb
    rwa [hordP] at h
  have htoP : toPoint W x y = WeierstrassCurve.Affine.Point.some x y nP := dif_pos nP
  rw [htoP, zero_zsmul, add_zero] at e
  intro hux
  subst hux
  by_cases hvy : v = W.toAffine.negY u y
  ·
    apply ha₂
    apply key
    have e2 : WeierstrassCurve.Affine.Point.some u v huv = -WeierstrassCurve.Affine.Point.some u y nP := by
      rw [WeierstrassCurve.Affine.Point.neg_some]
      subst hvy
      rfl
    rw [add_zsmul, one_zsmul, e, e2, neg_add_cancel]
  ·
    apply ha₁
    apply key
    have hvy' : v = y := WeierstrassCurve.Affine.Y_eq_of_Y_ne huv.left hxy rfl hvy
    have e2 : WeierstrassCurve.Affine.Point.some u v huv = WeierstrassCurve.Affine.Point.some u y nP := by
      subst hvy'
      rfl
    rw [sub_zsmul, one_zsmul, e, e2]
    exact add_neg_cancel _

end FieldCase2

theorem apply_ne_apply
    {A : Type} [CommRing A] (𝒢₀ : GroupLaws A) (h𝒢₀ : 𝒢₀.IsChordTangent) (h𝒢₀O : 𝒢₀.IsOriginIdentity)
    (q : ℕ) (𝒯₀ : LevelTransport A 𝒢₀ q) (h𝒯₀ : 𝒯₀.IsSectionTransport)
    (hVC₀ : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve.Projective T) (C : WeierstrassCurve.VariableChange T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (C • W))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (C • W)) ≤ (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
        IsVariableChangeHom W C φ)
    (hCO₀ : ∀ (T T' : Type) [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] (f : T →ₐ[A] T')
      (W : WeierstrassCurve.Projective T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (W.map f.toRingHom))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map f.toRingHom)) ≤
          (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
        IsCoefficientHom W f.toRingHom φ)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ)
    {T : Type} [CommRing T] [Algebra A T] {k : Type} [Field k] [Algebra A k] (f : T →ₐ[A] k)
    (x : RawDrinfeldPair T) (hΔ : IsUnit x.curve.Δ)
    (x₀ y₀ : T) (hS : IsSectionThrough x.P x₀ y₀) (hS' : IsSectionThrough x.Q x₀ y₀)
    (hx : (x.curve.preΨ ℓ).eval x₀ = 0)
    (a : ℤ) (ha : ¬ ((ℓ : ℤ) ∣ a)) (ha₁ : ¬ ((ℓ : ℤ) ∣ a - 1)) (ha₂ : ¬ ((ℓ : ℤ) ∣ a + 1))
    (x₁ y₁ : T) (hS₁ : IsSectionThrough (zlinComb (𝒢₀ T x.curve hΔ) x.P x.Q a 0) x₁ y₁) :
    f x₁ ≠ f x₀ := by

  obtain ⟨tP, tQ⟩ := WeierstrassCurve.DrinfeldGlobal.isSectionThrough_map_of_isSectionTransport A 𝒢₀ q 𝒯₀ h𝒯₀ f x
    (hCO₀ T k f _) ⟨x₀, y₀, x₀, y₀⟩ hS hS'
  obtain ⟨hc1, -⟩ := h𝒯₀.2 T k f x
  have hΔk : IsUnit (𝒯₀.map f x).curve.Δ := by rw [hc1, WeierstrassCurve.map_Δ]; exact hΔ.map _
  have hEk : (𝒯₀.map f x).curve.toAffine.Equation (f x₀) (f y₀) :=
    ((WeierstrassCurve.DrinfeldGlobal.equation_iff_exists_isSectionThrough_and_eq_iff_of_isSectionThrough _).1 _ _).mpr ⟨_, tP⟩
  have hxk : ((𝒯₀.map f x).curve.preΨ ℓ).eval (f x₀) = 0 := by
    rw [hc1, WeierstrassCurve.map_preΨ, Polynomial.eval_map]
    show Polynomial.eval₂ f.toRingHom (f.toRingHom x₀) (x.curve.preΨ ℓ) = 0
    rw [Polynomial.eval₂_at_apply, hx, map_zero]

  obtain ⟨u, v, huv, e⟩ := exists_zsmul_eq_some ℓ hℓ3 (𝒯₀.map f x).curve hΔk (f x₀) (f y₀) hEk hxk a ha
  have hux : u ≠ f x₀ := fst_ne_of_zsmul_eq_some ℓ hℓ3 (𝒯₀.map f x).curve hΔk (f x₀) (f y₀) hEk hxk a ha₁ ha₂ u v huv e
  obtain ⟨-, thr⟩ := WeierstrassCurve.DrinfeldGlobal.isSectionThrough_zlinComb_of_isSectionThrough A 𝒢₀ h𝒢₀ h𝒢₀O
    (𝒯₀.map f x).curve hΔk _ _ _ _ _ _ tP tQ a 0
  have hRk : IsSectionThrough (zlinComb (𝒢₀ k (𝒯₀.map f x).curve hΔk) (𝒯₀.map f x).P (𝒯₀.map f x).Q a 0) u v :=
    thr u v huv e

  let g : Matrix (Fin 2) (Fin 2) ℤ := !![a, 1; 0, 0]
  have hg0 : g 0 0 = a := rfl
  have hg1 : g 1 0 = 0 := rfl
  have hg01 : g 0 1 = 1 := rfl
  have hg11 : g 1 1 = 0 := rfl
  have eP : (RawDrinfeldPair.relabel 𝒢₀ g x hΔ).P = zlinComb (𝒢₀ T x.curve hΔ) x.P x.Q a 0 := by
    show zlinComb _ _ _ (g 0 0) (g 1 0) = _
    rw [hg0, hg1]
  have eQ : (RawDrinfeldPair.relabel 𝒢₀ g x hΔ).Q = x.P := by
    show zlinComb _ _ _ (g 0 1) (g 1 1) = _
    rw [hg01, hg11]
    exact zlinComb_one_zero _ _ _
  obtain ⟨tP₁, -⟩ := WeierstrassCurve.DrinfeldGlobal.isSectionThrough_map_of_isSectionTransport A 𝒢₀ q 𝒯₀ h𝒯₀ f
    (RawDrinfeldPair.relabel 𝒢₀ g x hΔ) (hCO₀ T k f _) ⟨x₁, y₁, x₀, y₀⟩ (by rw [eP]; exact hS₁) (by rw [eQ]; exact hS)
  have em := WeierstrassCurve.DrinfeldGlobal.LevelTransport.map_relabel_eq_relabel_map 𝒢₀ h𝒢₀ h𝒢₀O q 𝒯₀ h𝒯₀ hVC₀ hCO₀
    T k f g x hΔ hΔk
  have hRk₁ : IsSectionThrough (zlinComb (𝒢₀ k (𝒯₀.map f x).curve hΔk) (𝒯₀.map f x).P (𝒯₀.map f x).Q a 0) (f x₁) (f y₁) := by
    have h := tP₁
    rw [em] at h
    have e1 : (RawDrinfeldPair.relabel 𝒢₀ g (𝒯₀.map f x) hΔk).P =
        zlinComb (𝒢₀ k (𝒯₀.map f x).curve hΔk) (𝒯₀.map f x).P (𝒯₀.map f x).Q a 0 := by
      show zlinComb _ _ _ (g 0 0) (g 1 0) = _
      rw [hg0, hg1]
    rw [e1] at h
    exact h

  obtain ⟨hxeq, -⟩ := (((WeierstrassCurve.DrinfeldGlobal.equation_iff_exists_isSectionThrough_and_eq_iff_of_isSectionThrough
    (𝒯₀.map f x).curve).2 _ _ _ _ _ _ hRk hRk₁).mp rfl)
  rw [← hxeq]
  exact hux

end LBAux

open LBAux in
theorem solution
    {A : Type} [CommRing A] (𝒢 : GroupLaws A) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ)
    (T : Type) [CommRing T] [Algebra A T] (hℓT : IsUnit ((ℓ : ℕ) : T))
    (W : WeierstrassCurve.Projective T) (hΔ : IsUnit W.Δ)
    (S : Section W) (x y : T) (hS : IsSectionThrough S x y) (hx : (W.preΨ ℓ).eval x = 0)
    (a : ℤ) (ha : ¬ ((ℓ : ℤ) ∣ a)) (ha₁ : ¬ ((ℓ : ℤ) ∣ a - 1)) (ha₂ : ¬ ((ℓ : ℤ) ∣ a + 1))
    (x' y' : T) (hS' : IsSectionThrough (ModularCurve.LevelRelabelling.zsmulSection (𝒢 T W hΔ) a S) x' y') :
    IsUnit (x - x') := by
  haveI : W.toAffine.IsElliptic := ⟨hΔ⟩
  obtain ⟨𝒢₀, 𝒯₀, h𝒢₀, h𝒢₀O, h𝒯₀, hVC₀, hCO₀⟩ :=
    WeierstrassCurve.DrinfeldGlobal.exists_groupLaws_levelTransport_isChordTangent_isOriginIdentity_isSectionTransport A ℓ

  have h1 : ((𝒢 T W hΔ).one (𝟙 _)).1 = ((𝒢₀ T W hΔ).one (𝟙 _)).1 := by
    rw [(RelativeGroupLaw.exists_isOriginChartSection_iff_one_eq_kwZeroSect W (𝒢 T W hΔ)).mp (h𝒢O T W hΔ),
      (RelativeGroupLaw.exists_isOriginChartSection_iff_one_eq_kwZeroSect W (𝒢₀ T W hΔ)).mp (h𝒢₀O T W hΔ)]
  rw [← zlinComb_self_zero, zlinComb_eq_of_one_eq W _ _ h1] at hS'

  by_contra hnu
  obtain ⟨𝔪, h𝔪, hmem⟩ := exists_max_ideal_of_mem_nonunits (mem_nonunits_iff.mpr hnu)
  letI : Field (T ⧸ 𝔪) := Ideal.Quotient.field 𝔪
  have hne := apply_ne_apply 𝒢₀ h𝒢₀ h𝒢₀O ℓ 𝒯₀ h𝒯₀ hVC₀ hCO₀ ℓ hℓ3 (Ideal.Quotient.mkₐ A 𝔪)
    (⟨W, S, S⟩ : RawDrinfeldPair T) hΔ x y hS hS hx a ha ha₁ ha₂ x' y' hS'
  apply hne
  show Ideal.Quotient.mk 𝔪 x' = Ideal.Quotient.mk 𝔪 x
  rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem]
  have : x' - x = -(x - x') := by ring
  rw [this]
  exact 𝔪.neg_mem_iff.mpr hmem

end
end S_WeierstrassCurve_DrinfeldGlobal_isUnit_sub_of_isSectionThrough_zsmulSection_of_eval_prePsi_eq_zero
end P2MW
export P2MW.S_WeierstrassCurve_DrinfeldGlobal_isUnit_sub_of_isSectionThrough_zsmulSection_of_eval_prePsi_eq_zero (solution)
