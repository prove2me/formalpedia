-- Prove2me | solution 1 for WeierstrassCurve.exists_smul_abscissa_prod_X_sub_C_dvd_prePsi
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/0610a5f3-33ef-5c7f-b563-607b7150653b

import Mathlib
import Theorems.Thm_WeierstrassCurve_eval_prePsi_Phi_div_PsiSq_eq_zero_of_eval_prePsi_eq_zero
import Theorems.Thm_WeierstrassCurve_Affine_Point_zsmul_x_mul_psi_sq
import Theorems.Thm_WeierstrassCurve_Affine_evalEval_psi_sq
import Theorems.Thm_WeierstrassCurve_Affine_evalEval_phi
import Theorems.Thm_WeierstrassCurve_isCoprime_Phi_PsiSq
import Theorems.Thm_WeierstrassCurve_Affine_Point_nsmul_some_eq_zero_iff_eval_prePsi
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_smul_abscissa_prod_X_sub_C_dvd_prePsi
p2m_attr_erase "instance" "WeierstrassCurve.Generic.isElliptic_curve WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv"
p2m_attr_erase "simp" "WeierstrassCurve.Generic.poly_map_classify WeierstrassCurve.Generic.poly_a₆ WeierstrassCurve.Generic.poly_a₁ WeierstrassCurve.Generic.classify_X WeierstrassCurve.Generic.coeffs_two WeierstrassCurve.Generic.coeffs_one WeierstrassCurve.Generic.curve_a₄ WeierstrassCurve.Generic.coeffs_three WeierstrassCurve.Generic.poly_a₄ WeierstrassCurve.Generic.poly_a₃ WeierstrassCurve.Generic.poly_a₂ WeierstrassCurve.Generic.coeffs_zero WeierstrassCurve.Generic.curve_a₂ WeierstrassCurve.Generic.coeffs_four WeierstrassCurve.Generic.curve_a₆ WeierstrassCurve.Generic.curve_a₁ WeierstrassCurve.Generic.curve_a₃ compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

universe u

open Polynomial

namespace KerLine

theorem isUnit_of_forall_field {R : Type u} [CommRing R] (a : R)
    (h : ∀ (F : Type u) [Field F] (χ : R →+* F), χ a ≠ 0) : IsUnit a := by
  by_contra ha
  obtain ⟨M, hM, haM⟩ := exists_max_ideal_of_mem_nonunits (mem_nonunits_iff.mpr ha)
  letI : Field (R ⧸ M) := Ideal.Quotient.field M
  exact h (R ⧸ M) (Ideal.Quotient.mk M) (Ideal.Quotient.eq_zero_iff_mem.mpr haM)

theorem prod_X_sub_C_dvd {S : Type u} [CommRing S] {ι : Type} [DecidableEq ι] (s : Finset ι) (r : ι → S)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → IsUnit (r i - r j)) (F : S[X]) (hF : ∀ i ∈ s, F.eval (r i) = 0) :
    (∏ i ∈ s, (X - C (r i))) ∣ F := by
  induction s using Finset.induction_on generalizing F with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.prod_insert hi]
    have hroot : F.IsRoot (r i) := hF i (Finset.mem_insert_self i s)
    obtain ⟨F₁, hF₁⟩ : X - C (r i) ∣ F := dvd_iff_isRoot.mpr hroot
    have hF₁r : ∀ j ∈ s, F₁.eval (r j) = 0 := by
      intro j hj
      have hij : i ≠ j := fun h => hi (h ▸ hj)
      have hu : IsUnit (r j - r i) :=
        hsep j (Finset.mem_insert_of_mem hj) i (Finset.mem_insert_self i s) (Ne.symm hij)
      have := hF j (Finset.mem_insert_of_mem hj)
      rw [hF₁, eval_mul, eval_sub, eval_X, eval_C] at this
      exact (hu.mul_right_eq_zero).mp this
    obtain ⟨G, hG⟩ := ih (fun a ha b hb hab => hsep a (Finset.mem_insert_of_mem ha) b (Finset.mem_insert_of_mem hb) hab) F₁ hF₁r
    exact ⟨G, by rw [hF₁, hG, mul_assoc]⟩

section FieldCase

variable {K : Type u} [Field K] [DecidableEq K]

theorem xmul_field (W : WeierstrassCurve K) [W.IsElliptic] {m : ℤ} {x₀ y₀ : K} (h₀ : W.toAffine.Nonsingular x₀ y₀) {x₁ y₁ : K}
    (h₁ : W.toAffine.Nonsingular x₁ y₁)
    (hm : m • WeierstrassCurve.Affine.Point.some x₀ y₀ h₀ = WeierstrassCurve.Affine.Point.some x₁ y₁ h₁) :
    (W.ΨSq m).eval x₀ ≠ 0 ∧ x₁ * (W.ΨSq m).eval x₀ = (W.Φ m).eval x₀ := by
  have key := WeierstrassCurve.Affine.Point.zsmul_x_mul_psi_sq W m h₀ h₁ hm
  rw [WeierstrassCurve.Affine.evalEval_psi_sq W h₀.left m, WeierstrassCurve.Affine.evalEval_phi W h₀.left m] at key
  refine ⟨fun h0 => ?_, key⟩
  have hΦ : (W.Φ m).eval x₀ = 0 := by rw [← key, h0, mul_zero]
  obtain ⟨u, v, huv⟩ := WeierstrassCurve.isCoprime_Phi_PsiSq W m
  have := congrArg (Polynomial.eval x₀) huv
  rw [eval_add, eval_mul, eval_mul, hΦ, h0, mul_zero, mul_zero, add_zero, eval_one] at this
  exact zero_ne_one this

theorem some_eq_or_eq_neg (W : WeierstrassCurve K) {x y₁ y₂ : K} (h₁ : W.toAffine.Nonsingular x y₁) (h₂ : W.toAffine.Nonsingular x y₂) :
    WeierstrassCurve.Affine.Point.some x y₁ h₁ = WeierstrassCurve.Affine.Point.some x y₂ h₂ ∨
      WeierstrassCurve.Affine.Point.some x y₁ h₁ = -WeierstrassCurve.Affine.Point.some x y₂ h₂ := by
  have e₁ := (WeierstrassCurve.Affine.equation_iff _ _).mp h₁.left
  have e₂ := (WeierstrassCurve.Affine.equation_iff _ _).mp h₂.left
  have key : (y₁ - y₂) * (y₁ - W.toAffine.negY x y₂) = 0 := by
    rw [WeierstrassCurve.Affine.negY]; linear_combination e₁ - e₂
  rcases mul_eq_zero.mp key with h | h
  · left
    have : y₁ = y₂ := sub_eq_zero.mp h
    subst this; rfl
  · right
    rw [WeierstrassCurve.Affine.Point.neg_some]
    have : y₁ = W.toAffine.negY x y₂ := sub_eq_zero.mp h
    subst this; rfl

theorem smul_abscissa_ne (W : WeierstrassCurve K) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ2 : ℓ ≠ 2) (hΔ : W.Δ ≠ 0)
    {x₀ y₀ : K} (h₀ : W.toAffine.Nonsingular x₀ y₀) (hx : (W.preΨ ℓ).eval x₀ = 0)
    (a b : ℕ) (ha1 : 1 ≤ a) (ha2 : a ≤ (ℓ - 1) / 2) (hb1 : 1 ≤ b) (hb2 : b ≤ (ℓ - 1) / 2) (hab : a ≠ b)
    (ra rb : K) (hra : ra * (W.ΨSq a).eval x₀ = (W.Φ a).eval x₀) (hrb : rb * (W.ΨSq b).eval x₀ = (W.Φ b).eval x₀)
    (hua : (W.ΨSq a).eval x₀ ≠ 0) (hub : (W.ΨSq b).eval x₀ ≠ 0) : ra ≠ rb := by
  have hp : ℓ.Prime := Fact.out
  haveI : NeZero ℓ := ⟨hp.ne_zero⟩
  have hodd : Odd ℓ := hp.odd_of_ne_two hℓ2
  haveI : W.IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ⟩
  set P : W.toAffine.Point := WeierstrassCurve.Affine.Point.some x₀ y₀ h₀ with hPdef
  have hℓP : (ℓ : ℤ) • P = 0 := by
    rw [natCast_zsmul, hPdef]
    refine (WeierstrassCurve.Affine.Point.nsmul_some_eq_zero_iff_eval_prePsi W hodd h₀).mpr ?_
    rw [← WeierstrassCurve.preΨ_ofNat]; exact hx
  have hP0 : P ≠ 0 := WeierstrassCurve.Affine.Point.some_ne_zero _
  have hprime : Prime (ℓ : ℤ) := Nat.prime_iff_prime_int.mp hp

  have hiff : ∀ m : ℤ, m • P = 0 → (ℓ : ℤ) ∣ m := by
    intro m hm
    by_contra hdvd
    have hcopN : Nat.Coprime ℓ m.natAbs :=
      (Nat.Prime.coprime_iff_not_dvd hp).mpr (fun h0 => hdvd (Int.natCast_dvd.mpr h0))
    have hcop : IsCoprime (ℓ : ℤ) m := by
      rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_eq_natAbs, Int.natAbs_natCast]; exact hcopN
    obtain ⟨u, v, huv⟩ := hcop
    apply hP0
    calc P = (1 : ℤ) • P := (one_zsmul P).symm
      _ = (u * ℓ + v * m) • P := by rw [huv]
      _ = u • ((ℓ : ℤ) • P) + v • (m • P) := by rw [add_zsmul, mul_zsmul, mul_zsmul]
      _ = 0 := by rw [hℓP, hm, zsmul_zero, zsmul_zero, add_zero]
  have hl2 : 2 * ((ℓ - 1) / 2) < ℓ := by obtain ⟨k, hk⟩ := hodd; omega

  have hmul : ∀ (c : ℕ) (rc : K), 1 ≤ c → c ≤ (ℓ - 1) / 2 → rc * (W.ΨSq c).eval x₀ = (W.Φ c).eval x₀ → (W.ΨSq c).eval x₀ ≠ 0 →
      ∃ (yc : K) (hc : W.toAffine.Nonsingular rc yc), ((c : ℕ) : ℤ) • P = WeierstrassCurve.Affine.Point.some rc yc hc := by
    intro c rc hc1 hc2 hrc huc
    have hcP : ((c : ℕ) : ℤ) • P ≠ 0 := by
      intro h0; have := Int.le_of_dvd (by exact_mod_cast hc1) (hiff _ h0); omega
    obtain ⟨xc, yc, nc, ec⟩ : ∃ (xc yc : K) (nc : W.toAffine.Nonsingular xc yc),
        ((c : ℕ) : ℤ) • P = WeierstrassCurve.Affine.Point.some xc yc nc := by
      cases hQ : ((c : ℕ) : ℤ) • P with
      | zero => exact absurd hQ hcP
      | some xc yc nc => exact ⟨xc, yc, nc, rfl⟩
    obtain ⟨-, hxc⟩ := xmul_field W h₀ nc (by rw [← hPdef]; exact ec)
    have : xc = rc := by
      have := hxc.trans hrc.symm
      exact mul_right_cancel₀ huc this
    subst this
    exact ⟨yc, nc, ec⟩
  intro heq
  obtain ⟨ya, na, ea⟩ := hmul a ra ha1 ha2 hra hua
  obtain ⟨yb, nb, eb⟩ := hmul b rb hb1 hb2 hrb hub
  subst heq
  rcases some_eq_or_eq_neg W na nb with h | h
  ·
    have : (((a : ℕ) : ℤ) - ((b : ℕ) : ℤ)) • P = 0 := by rw [sub_zsmul, ea, eb, h]; abel
    have := Int.eq_zero_of_abs_lt_dvd (hiff _ this) (by rw [abs_lt]; constructor <;> omega)
    omega
  ·
    have : (((a : ℕ) : ℤ) + ((b : ℕ) : ℤ)) • P = 0 := by rw [add_zsmul, ea, eb, h]; abel
    have := Int.eq_zero_of_abs_lt_dvd (hiff _ this) (by rw [abs_lt]; constructor <;> omega)
    omega

end FieldCase

theorem hom_eval {R S : Type u} [CommRing R] [CommRing S] (χ : R →+* S) (p : R[X]) (a : R) :
    χ (p.eval a) = (p.map χ).eval (χ a) := by
  rw [eval_map, eval₂_at_apply]

theorem exists_equation {K : Type u} [Field K] [IsAlgClosed K] (W : WeierstrassCurve K) (x : K) :
    ∃ y : K, W.toAffine.Equation x y := by
  let q : K[X] := X ^ 2 + (C (W.a₁ * x + W.a₃) * X - C (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆))
  have hq : q.degree = 2 := by
    show (X ^ 2 + (C (W.a₁ * x + W.a₃) * X - C (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆))).degree = 2
    rw [degree_add_eq_left_of_degree_lt, degree_X_pow]; · rfl
    rw [degree_X_pow]
    refine (degree_sub_le _ _).trans_lt ?_
    rw [max_lt_iff]
    exact ⟨(degree_C_mul_X_le _).trans_lt (by norm_num), degree_C_le.trans_lt (by norm_num)⟩
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_root q (by rw [hq]; norm_num)
  refine ⟨y, ?_⟩
  have h : y ^ 2 + ((W.a₁ * x + W.a₃) * y - (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆)) = 0 := by
    have := hy
    simp only [q, IsRoot, eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C] at this
    exact this
  rw [WeierstrassCurve.Affine.equation_iff]
  linear_combination h

end KerLine

open KerLine in
theorem solution
    {T : Type u} [CommRing T] (W : WeierstrassCurve T) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ2 : ℓ ≠ 2)
    (hℓΔ : IsUnit ((ℓ : T) * W.Δ)) (x : T) (hx : (W.preΨ ℓ).eval x = 0) :
    ∃ r : ℕ → T,
      (∀ a : ℕ, 1 ≤ a → a ≤ (ℓ - 1) / 2 →
        IsUnit ((W.ΨSq a).eval x) ∧ r a * (W.ΨSq a).eval x = (W.Φ a).eval x) ∧
      (∀ a b : ℕ, 1 ≤ a → a ≤ (ℓ - 1) / 2 → 1 ≤ b → b ≤ (ℓ - 1) / 2 → a ≠ b → IsUnit (r a - r b)) ∧
      (∏ a ∈ Finset.Icc 1 ((ℓ - 1) / 2), (X - C (r a))) ∣ W.preΨ ℓ := by
  classical
  have hp : ℓ.Prime := Fact.out
  have hndvd : ∀ a : ℕ, 1 ≤ a → a ≤ (ℓ - 1) / 2 → ¬ ((ℓ : ℤ) ∣ (a : ℤ)) := by
    intro a ha1 ha2 h
    have hodd : Odd ℓ := hp.odd_of_ne_two hℓ2
    have hl2 : 2 * ((ℓ - 1) / 2) < ℓ := by obtain ⟨k, hk⟩ := hodd; omega
    have := Int.le_of_dvd (by exact_mod_cast ha1) h
    omega

  let r : ℕ → T := fun a => (W.Φ a).eval x * Ring.inverse ((W.ΨSq a).eval x)
  have hr : ∀ a : ℕ, 1 ≤ a → a ≤ (ℓ - 1) / 2 →
      IsUnit ((W.ΨSq a).eval x) ∧ r a * (W.ΨSq a).eval x = (W.Φ a).eval x ∧ (W.preΨ ℓ).eval (r a) = 0 := by
    intro a ha1 ha2
    obtain ⟨hu, hroot⟩ := WeierstrassCurve.eval_prePsi_Phi_div_PsiSq_eq_zero_of_eval_prePsi_eq_zero W hℓ2 hℓΔ hx (hndvd a ha1 ha2)
    exact ⟨hu, by rw [show r a = _ from rfl, mul_assoc, Ring.inverse_mul_cancel _ hu, mul_one], hroot⟩

  have hdiff : ∀ a b : ℕ, 1 ≤ a → a ≤ (ℓ - 1) / 2 → 1 ≤ b → b ≤ (ℓ - 1) / 2 → a ≠ b → IsUnit (r a - r b) := by
    intro a b ha1 ha2 hb1 hb2 hab
    apply isUnit_of_forall_field
    intro F _ χ h0

    let K := AlgebraicClosure F
    let φ : T →+* K := (algebraMap F K).comp χ
    have h0K : φ (r a) = φ (r b) := by
      have : χ (r a) = χ (r b) := sub_eq_zero.mp (by rw [← map_sub]; exact h0)
      show algebraMap F K (χ (r a)) = algebraMap F K (χ (r b)); rw [this]
    obtain ⟨hua, hra, -⟩ := hr a ha1 ha2
    obtain ⟨hub, hrb, -⟩ := hr b hb1 hb2
    have hΔK : (W.map φ).Δ ≠ 0 := by
      rw [WeierstrassCurve.map_Δ]; exact ((isUnit_of_mul_isUnit_right hℓΔ).map φ).ne_zero
    have hxK : ((W.map φ).preΨ ℓ).eval (φ x) = 0 := by
      rw [WeierstrassCurve.map_preΨ, ← hom_eval, hx, map_zero]
    obtain ⟨y₀, hy₀⟩ := exists_equation (W.map φ) (φ x)
    have n₀ : (W.map φ).toAffine.Nonsingular (φ x) y₀ := (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero hΔK).mp hy₀
    have hra' : φ (r a) * ((W.map φ).ΨSq a).eval (φ x) = ((W.map φ).Φ a).eval (φ x) := by
      rw [WeierstrassCurve.map_ΨSq, WeierstrassCurve.map_Φ, ← hom_eval, ← hom_eval, ← map_mul, hra]
    have hrb' : φ (r b) * ((W.map φ).ΨSq b).eval (φ x) = ((W.map φ).Φ b).eval (φ x) := by
      rw [WeierstrassCurve.map_ΨSq, WeierstrassCurve.map_Φ, ← hom_eval, ← hom_eval, ← map_mul, hrb]
    have hua' : ((W.map φ).ΨSq a).eval (φ x) ≠ 0 := by
      rw [WeierstrassCurve.map_ΨSq, ← hom_eval]; exact (hua.map φ).ne_zero
    have hub' : ((W.map φ).ΨSq b).eval (φ x) ≠ 0 := by
      rw [WeierstrassCurve.map_ΨSq, ← hom_eval]; exact (hub.map φ).ne_zero
    exact smul_abscissa_ne (W.map φ) ℓ hℓ2 hΔK n₀ hxK a b ha1 ha2 hb1 hb2 hab (φ (r a)) (φ (r b)) hra' hrb' hua' hub' h0K
  refine ⟨r, fun a h1 h2 => ⟨(hr a h1 h2).1, (hr a h1 h2).2.1⟩, hdiff, ?_⟩
  refine prod_X_sub_C_dvd (Finset.Icc 1 ((ℓ - 1) / 2)) r ?_ (W.preΨ ℓ) ?_
  · intro i hi j hj hij
    obtain ⟨hi1, hi2⟩ := Finset.mem_Icc.mp hi
    obtain ⟨hj1, hj2⟩ := Finset.mem_Icc.mp hj
    exact hdiff i j hi1 hi2 hj1 hj2 hij
  · intro i hi
    obtain ⟨hi1, hi2⟩ := Finset.mem_Icc.mp hi
    exact (hr i hi1 hi2).2.2

end S_WeierstrassCurve_exists_smul_abscissa_prod_X_sub_C_dvd_prePsi
end P2MW
export P2MW.S_WeierstrassCurve_exists_smul_abscissa_prod_X_sub_C_dvd_prePsi (solution)
