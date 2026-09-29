-- Prove2me | solution 1 for WeierstrassCurve.exists_hauptmodulFive_of_not_modRepIsIrreducible
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/375631dd-f5c6-5525-b3bd-cfc7b3ba66e3

import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms
import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Algebra.Rat
import Definitions.Def_FLTPrelim_ModularRep
import Theorems.Thm_WeierstrassCurve_card_torsion_of_isAlgClosed
import Theorems.Thm_WeierstrassCurve_Affine_Point_smul_some_eq_zero_iff
import Theorems.Thm_WeierstrassCurve_Affine_Point_zsmul_some_eq_some_div
import Theorems.Thm_WeierstrassCurve_Affine_Point_two_smul_some_eq_zero_iff
import Theorems.Thm_Submodule_eq_span_singleton_of_card_eq_sq
import Theorems.Thm_ModularCurve_exists_hauptmodulFive_of_kernelQuadratic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_hauptmodulFive_of_not_modRepIsIrreducible
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point Polynomial

open scoped WeierstrassCurve.Affine

namespace M4cP4Five

theorem map_add_eq_and_map_mul_eq_of_mem_pair {K : Type*} [CommRing K] (f : K →+* K)
    (hinj : Function.Injective f) {a b : K} (hab : a ≠ b)
    (ha : f a = a ∨ f a = b) (hb : f b = a ∨ f b = b) :
    f (a + b) = a + b ∧ f (a * b) = a * b := by
  have hfab : f a ≠ f b := fun h => hab (hinj h)
  rcases ha with ha | ha
  · have hb' : f b = b := by
      rcases hb with hb | hb
      · exact absurd (ha.trans hb.symm) hfab
      · exact hb
    rw [map_add, map_mul, ha, hb']
    exact ⟨rfl, rfl⟩
  · have hb' : f b = a := by
      rcases hb with hb | hb
      · exact hb
      · exact absurd (ha.trans hb.symm) hfab
    rw [map_add, map_mul, ha, hb']
    exact ⟨add_comm b a, mul_comm b a⟩

theorem duplicationClosed_of_swapped {F : Type*} [Field F] (A B X₁ X₂ : F) (hne : X₁ ≠ X₂)
    (hD₁ : X₂ * (4 * X₁ ^ 3 + 4 * A * X₁ + 4 * B) = X₁ ^ 4 - 2 * A * X₁ ^ 2 - 8 * B * X₁ + A ^ 2)
    (hD₂ : X₁ * (4 * X₂ ^ 3 + 4 * A * X₂ + 4 * B) = X₂ ^ 4 - 2 * A * X₂ ^ 2 - 8 * B * X₂ + A ^ 2) :
    (2 * A * (-(X₁ + X₂)) - 4 * B - (-(X₁ + X₂)) ^ 3
        + 6 * (-(X₁ + X₂)) * (X₁ * X₂) = 0) ∧
    (A ^ 2 - 2 * A * (X₁ * X₂) + 4 * B * (-(X₁ + X₂))
        - (-(X₁ + X₂)) ^ 2 * (X₁ * X₂) + 5 * (X₁ * X₂) ^ 2 = 0) := by

  have e₁ : (2 * A * (-(X₁ + X₂)) - 4 * B - (-(X₁ + X₂)) ^ 3
        + 6 * (-(X₁ + X₂)) * (X₁ * X₂)) * X₁
      + (A ^ 2 - 2 * A * (X₁ * X₂) + 4 * B * (-(X₁ + X₂))
          - (-(X₁ + X₂)) ^ 2 * (X₁ * X₂) + 5 * (X₁ * X₂) ^ 2) = 0 := by
    linear_combination (-1 : F) * hD₁
  have e₂ : (2 * A * (-(X₁ + X₂)) - 4 * B - (-(X₁ + X₂)) ^ 3
        + 6 * (-(X₁ + X₂)) * (X₁ * X₂)) * X₂
      + (A ^ 2 - 2 * A * (X₁ * X₂) + 4 * B * (-(X₁ + X₂))
          - (-(X₁ + X₂)) ^ 2 * (X₁ * X₂) + 5 * (X₁ * X₂) ^ 2) = 0 := by
    linear_combination (-1 : F) * hD₂
  have h₃ : (2 * A * (-(X₁ + X₂)) - 4 * B - (-(X₁ + X₂)) ^ 3
      + 6 * (-(X₁ + X₂)) * (X₁ * X₂)) * (X₁ - X₂) = 0 := by
    linear_combination e₁ - e₂
  have hg₃ : 2 * A * (-(X₁ + X₂)) - 4 * B - (-(X₁ + X₂)) ^ 3
      + 6 * (-(X₁ + X₂)) * (X₁ * X₂) = 0 := by
    rcases mul_eq_zero.mp h₃ with h | h
    · exact h
    · exact absurd (sub_eq_zero.mp h) hne
  refine ⟨hg₃, ?_⟩
  linear_combination e₁ - X₁ * hg₃

section GaloisHalf

theorem toShortNF_u (V : WeierstrassCurve ℚ) [Invertible (2 : ℚ)] [Invertible (3 : ℚ)] :
    V.toShortNF.u = 1 := by
  simp [toShortNF, toCharNeTwoNF, VariableChange.mul_def]

local notation "Qb" => AlgebraicClosure ℚ

theorem exists_rational_kernelQuadratic (V : WeierstrassCurve ℚ) (hΔ : V.Δ ≠ 0)
    [Invertible (2 : ℚ)] [Invertible (3 : ℚ)]
    (h5 : ¬ GaloisRepIsIrreducible (K := Qb) ℚ V 5) :
    ∃ p q : ℚ,
      p ^ 2 - 4 * q ≠ 0 ∧
      (2 * (V.toShortNF • V).a₄ * p - 4 * (V.toShortNF • V).a₆ - p ^ 3 + 6 * p * q = 0) ∧
      ((V.toShortNF • V).a₄ ^ 2 - 2 * (V.toShortNF • V).a₄ * q
        + 4 * (V.toShortNF • V).a₆ * p - p ^ 2 * q + 5 * q ^ 2 = 0) := by
  haveI hell : V.IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ⟩

  have hu : V.toShortNF.u = 1 := toShortNF_u V
  have hui : V.toShortNF.u⁻¹ = 1 := by rw [hu, inv_one]
  have eb₂ := V.variableChange_b₂ V.toShortNF
  have eb₄ := V.variableChange_b₄ V.toShortNF
  have eb₆ := V.variableChange_b₆ V.toShortNF
  have eb₈ := V.variableChange_b₈ V.toShortNF
  rw [b₂_of_isShortNF, hui, Units.val_one, one_pow, one_mul] at eb₂
  rw [b₄_of_isShortNF, hui, Units.val_one, one_pow, one_mul] at eb₄
  rw [b₆_of_isShortNF, hui, Units.val_one, one_pow, one_mul] at eb₆
  rw [b₈_of_isShortNF, hui, Units.val_one, one_pow, one_mul] at eb₈
  set r : ℚ := V.toShortNF.r with hr
  set A : ℚ := (V.toShortNF • V).a₄ with hA
  set B : ℚ := (V.toShortNF • V).a₆ with hB
  have hb₂ : V.b₂ = -12 * r := by linear_combination -eb₂
  rw [hb₂] at eb₄
  have hb₄ : V.b₄ = 2 * A + 6 * r ^ 2 := by linear_combination -eb₄
  rw [hb₂, hb₄] at eb₆
  have hb₆ : V.b₆ = 4 * B - 4 * A * r - 4 * r ^ 3 := by linear_combination -eb₆
  rw [hb₂, hb₄, hb₆] at eb₈
  have hb₈ : V.b₈ = -A ^ 2 - 12 * B * r + 6 * A * r ^ 2 + 3 * r ^ 4 := by
    linear_combination -eb₈

  have hcases : ∀ d : ZMod 5, d = 0 ∨ d = 1 ∨ d = 2 ∨ d = -2 ∨ d = -1 := by decide
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩

  haveI hnormQ : Normal ℚ Qb := by
    have h : @Normal ℚ Qb _ _ (AlgebraicClosure.instAlgebra ℚ) := inferInstance
    exact h
  haveI halgQ : Algebra.IsAlgebraic ℚ Qb := by
    have h : @Algebra.IsAlgebraic ℚ Qb _ _ (AlgebraicClosure.instAlgebra ℚ) := inferInstance
    exact h
  haveI hsepQ : Algebra.IsSeparable ℚ Qb := by
    have h : @Algebra.IsSeparable ℚ Qb _ _ (AlgebraicClosure.instAlgebra ℚ) := inferInstance
    exact h
  haveI : IsGalois ℚ Qb := ⟨⟩

  set E : WeierstrassCurve Qb := V.baseChange Qb with hE
  obtain ⟨ρ, hρ⟩ : ∃ ρ : Qb, algebraMap ℚ Qb r = ρ := ⟨_, rfl⟩
  obtain ⟨α, hα⟩ : ∃ α : Qb, algebraMap ℚ Qb A = α := ⟨_, rfl⟩
  obtain ⟨β, hβ⟩ : ∃ β : Qb, algebraMap ℚ Qb B = β := ⟨_, rfl⟩
  have hΨeval : ∀ x : Qb, E.Ψ₂Sq.eval x
      = 4 * x ^ 3 + algebraMap ℚ Qb V.b₂ * x ^ 2 + 2 * algebraMap ℚ Qb V.b₄ * x
        + algebraMap ℚ Qb V.b₆ := by
    intro x
    simp only [hE, WeierstrassCurve.baseChange, WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.map_b₂,
      WeierstrassCurve.map_b₄, WeierstrassCurve.map_b₆, eval_add, eval_mul, eval_pow, eval_C,
      eval_X]
  have hΦeval : ∀ x : Qb, (E.Φ 2).eval x
      = x ^ 4 - algebraMap ℚ Qb V.b₄ * x ^ 2 - 2 * algebraMap ℚ Qb V.b₆ * x
        - algebraMap ℚ Qb V.b₈ := by
    intro x
    rw [WeierstrassCurve.Φ_two]
    simp only [hE, WeierstrassCurve.baseChange, WeierstrassCurve.map_b₄,
      WeierstrassCurve.map_b₆, WeierstrassCurve.map_b₈, eval_sub, eval_mul, eval_pow,
      eval_C, eval_X]

  have hb₂K : algebraMap ℚ Qb V.b₂ = -12 * ρ := by
    have h := congrArg (algebraMap ℚ Qb) hb₂
    simp only [map_mul, map_neg, map_ofNat, hρ] at h
    linear_combination h
  have hb₄K : algebraMap ℚ Qb V.b₄ = 2 * α + 6 * ρ ^ 2 := by
    have h := congrArg (algebraMap ℚ Qb) hb₄
    simp only [map_add, map_mul, map_pow, map_ofNat, hρ, hα] at h
    linear_combination h
  have hb₆K : algebraMap ℚ Qb V.b₆ = 4 * β - 4 * α * ρ - 4 * ρ ^ 3 := by
    have h := congrArg (algebraMap ℚ Qb) hb₆
    simp only [map_sub, map_mul, map_pow, map_ofNat, hρ, hα, hβ] at h
    linear_combination h
  have hb₈K : algebraMap ℚ Qb V.b₈ = -α ^ 2 - 12 * β * ρ + 6 * α * ρ ^ 2 + 3 * ρ ^ 4 := by
    have h := congrArg (algebraMap ℚ Qb) hb₈
    simp only [map_add, map_sub, map_mul, map_neg, map_pow, map_ofNat, hρ, hα, hβ] at h
    linear_combination h

  have hevalσ : ∀ (f : ℚ[X]) (σ : Qb ≃ₐ[ℚ] Qb) (x : Qb),
      σ ((f.map (algebraMap ℚ Qb)).eval x) = (f.map (algebraMap ℚ Qb)).eval (σ x) := by
    intro f σ x
    rw [Polynomial.eval_map, Polynomial.eval_map, ← Polynomial.aeval_def, ← Polynomial.aeval_def]
    exact (Polynomial.aeval_algHom_apply σ x f).symm
  have hΨσ : ∀ (σ : Qb ≃ₐ[ℚ] Qb) (x : Qb), σ ((E.ΨSq 2).eval x) = (E.ΨSq 2).eval (σ x) := by
    intro σ x
    have hmap : E.ΨSq 2 = (V.ΨSq 2).map (algebraMap ℚ Qb) := V.map_ΨSq (algebraMap ℚ Qb) 2
    rw [hmap]
    exact hevalσ _ σ x
  have hΨSq : E.ΨSq 2 = E.Ψ₂Sq := E.ΨSq_two
  have hΦσ : ∀ (σ : Qb ≃ₐ[ℚ] Qb) (x : Qb), σ ((E.Φ 2).eval x) = (E.Φ 2).eval (σ x) := by
    intro σ x
    have hmap : E.Φ 2 = (V.Φ 2).map (algebraMap ℚ Qb) := V.map_Φ (algebraMap ℚ Qb) 2
    rw [hmap]
    exact hevalσ _ σ x

  have hcard : Nat.card (Submodule.torsionBy ℤ (V⁄Qb).Point (5 : ℕ)) = 5 ^ 2 :=
    WeierstrassCurve.card_torsion_of_isAlgClosed V (by norm_num)
  haveI : Finite (Submodule.torsionBy ℤ (V⁄Qb).Point (5 : ℕ)) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hnt : Nontrivial (Submodule.torsionBy ℤ (V⁄Qb).Point (5 : ℕ)) :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hcard]; norm_num)

  have hN : ∃ N : Submodule (ZMod 5) (Submodule.torsionBy ℤ (V⁄Qb).Point (5 : ℕ)),
      IsGaloisStable ℚ N ∧ N ≠ ⊥ ∧ N ≠ ⊤ := by
    by_contra hno
    refine h5 ⟨hnt, fun N hN => ?_⟩
    by_contra hcon
    rw [not_or] at hcon
    exact hno ⟨N, hN, hcon.1, hcon.2⟩
  obtain ⟨N, hN, hbot, htop⟩ := hN

  obtain ⟨T, hTN, hT0⟩ := (Submodule.ne_bot_iff N).mp hbot
  have hspan : N = Submodule.span (ZMod 5) {T} :=
    Submodule.eq_span_singleton_of_card_eq_sq hcard N htop hTN hT0

  have hP0 : (T : (V⁄Qb).Point) ≠ 0 := fun h => hT0 (Subtype.ext h)
  have h5P : (5 : ℕ) • (T : (V⁄Qb).Point) = 0 := by
    have h := (Submodule.mem_torsionBy_iff _ _).mp T.2
    exact_mod_cast h
  have hord : addOrderOf (T : (V⁄Qb).Point) = 5 := addOrderOf_eq_prime h5P hP0
  have hkP : ∀ k : ℕ, ¬ 5 ∣ k → k • (T : (V⁄Qb).Point) ≠ 0 := fun k hk h =>
    hk (hord ▸ addOrderOf_dvd_iff_nsmul_eq_zero.mpr h)
  have h2P0 : (2 : ℕ) • (T : (V⁄Qb).Point) ≠ 0 := hkP 2 (by norm_num)
  have h4P : (2 : ℕ) • ((2 : ℕ) • (T : (V⁄Qb).Point)) = -(T : (V⁄Qb).Point) := by
    rw [← mul_nsmul, eq_neg_iff_add_eq_zero, ← succ_nsmul]
    exact h5P

  rcases hT_eq : (T : (V⁄Qb).Point) with _ | ⟨x₁, y₁, h₁⟩
  · exact absurd hT_eq hP0
  rw [hT_eq] at h2P0 h4P hkP

  have hΨ₁ : E.Ψ₂Sq.eval x₁ ≠ 0 := fun h =>
    h2P0 ((WeierstrassCurve.Affine.Point.two_smul_some_eq_zero_iff E h₁).mpr h)
  have hψ₁ : (E.ψ 2).evalEval x₁ y₁ ≠ 0 := fun h => h2P0 (by
    rw [← ofNat_zsmul]
    exact (WeierstrassCurve.Affine.Point.smul_some_eq_zero_iff E h₁ 2).mpr h)
  obtain ⟨y₂, h₂, h2T⟩ :=
    WeierstrassCurve.Affine.Point.zsmul_some_eq_some_div E h₁ (n := 2) hψ₁
  set x₂ : Qb := (E.Φ 2).eval x₁ / (E.ΨSq 2).eval x₁ with hx₂
  have h2T' : (2 : ℕ) • (Point.some x₁ y₁ h₁) = Point.some x₂ y₂ h₂ := by
    rw [← ofNat_zsmul]
    exact h2T
  rw [h2T'] at h4P
  have hΨ₂ : E.Ψ₂Sq.eval x₂ ≠ 0 := fun h => by
    have h0 : (2 : ℕ) • (Point.some x₂ y₂ h₂) = 0 :=
      (WeierstrassCurve.Affine.Point.two_smul_some_eq_zero_iff E h₂).mpr h
    rw [h4P, neg_eq_zero] at h0
    exact absurd h0 (Point.some_ne_zero _)
  have hψ₂ : (E.ψ 2).evalEval x₂ y₂ ≠ 0 := fun h => by
    have h0 : (2 : ℕ) • (Point.some x₂ y₂ h₂) = 0 := by
      rw [← ofNat_zsmul]
      exact (WeierstrassCurve.Affine.Point.smul_some_eq_zero_iff E h₂ 2).mpr h
    rw [h4P, neg_eq_zero] at h0
    exact absurd h0 (Point.some_ne_zero _)
  obtain ⟨y₃, h₃, h4T⟩ :=
    WeierstrassCurve.Affine.Point.zsmul_some_eq_some_div E h₂ (n := 2) hψ₂
  have hx₁ : (E.Φ 2).eval x₂ / (E.ΨSq 2).eval x₂ = x₁ := by
    have h : Point.some ((E.Φ 2).eval x₂ / (E.ΨSq 2).eval x₂) y₃ h₃
        = -Point.some x₁ y₁ h₁ := by
      rw [← h4T, ofNat_zsmul, h4P]
    rw [Affine.Point.neg_some] at h
    exact (Point.some.inj h).1

  have R₁ : x₂ * E.Ψ₂Sq.eval x₁ = (E.Φ 2).eval x₁ := by
    rw [hx₂, ← hΨSq]
    exact div_mul_cancel₀ _ (by rw [hΨSq]; exact hΨ₁)
  have R₂ : x₁ * E.Ψ₂Sq.eval x₂ = (E.Φ 2).eval x₂ := by
    rw [← hx₁, ← hΨSq]
    exact div_mul_cancel₀ _ (by rw [hΨSq]; exact hΨ₂)

  have hne : x₁ ≠ x₂ := by
    intro h
    rcases (Point.X_eq_iff (h₁ := h₁) (h₂ := h₂)).mp h with h' | h'
    ·
      have h'' : Point.some x₁ y₁ h₁ + Point.some x₁ y₁ h₁ = Point.some x₁ y₁ h₁ := by
        rw [← two_nsmul, h2T', ← h']
      exact absurd (add_eq_left.mp h'') (Point.some_ne_zero h₁)
    ·
      apply hkP 3 (by norm_num)
      rw [succ_nsmul, h2T', h', add_neg_cancel]

  have horbit₁ : ∀ σ : Qb ≃ₐ[ℚ] Qb, σ x₁ = x₁ ∨ σ x₁ = x₂ := by
    intro σ
    have hmem : σ • T ∈ N := hN σ T hTN
    rw [hspan, Submodule.mem_span_singleton] at hmem
    obtain ⟨c, hc⟩ := hmem
    have hcoe : ((σ • T : Submodule.torsionBy ℤ (V⁄Qb).Point (5 : ℕ)) : (V⁄Qb).Point)
        = Point.map σ.toAlgHom (T : (V⁄Qb).Point) := rfl
    rw [hT_eq, Point.map_some] at hcoe
    rcases hcases c with rfl | rfl | rfl | rfl | rfl
    ·
      rw [zero_smul] at hc
      have h0 := congrArg Subtype.val hc
      rw [hcoe] at h0
      exact absurd h0.symm (Point.some_ne_zero _)
    ·
      rw [one_smul] at hc
      have h1 := congrArg Subtype.val hc
      rw [hcoe, hT_eq] at h1
      exact Or.inl (Point.some.inj h1).1.symm
    ·
      rw [two_smul] at hc
      have h2 := congrArg Subtype.val hc
      rw [Submodule.coe_add, hcoe, hT_eq, ← two_nsmul, h2T'] at h2
      exact Or.inr (Point.some.inj h2).1.symm
    ·
      rw [neg_smul, two_smul] at hc
      have h2 := congrArg Subtype.val hc
      rw [Submodule.coe_neg, Submodule.coe_add, hcoe, hT_eq, ← two_nsmul, h2T',
        Affine.Point.neg_some] at h2
      exact Or.inr (Point.some.inj h2).1.symm
    ·
      rw [neg_one_smul] at hc
      have h2 := congrArg Subtype.val hc
      rw [Submodule.coe_neg, hcoe, hT_eq, Affine.Point.neg_some] at h2
      exact Or.inl (Point.some.inj h2).1.symm

  have horbit₂ : ∀ σ : Qb ≃ₐ[ℚ] Qb, σ x₂ = x₁ ∨ σ x₂ = x₂ := by
    intro σ
    have hσx₂ : σ x₂ = (E.Φ 2).eval (σ x₁) / (E.ΨSq 2).eval (σ x₁) := by
      rw [hx₂, map_div₀, hΦσ, hΨσ]
    rcases horbit₁ σ with h | h
    · right
      rw [hσx₂, h]
    · left
      rw [hσx₂, h, hx₁]

  have hfix : ∀ σ : Qb ≃ₐ[ℚ] Qb, σ (x₁ + x₂) = x₁ + x₂ ∧ σ (x₁ * x₂) = x₁ * x₂ := fun σ =>
    map_add_eq_and_map_mul_eq_of_mem_pair (σ : Qb →+* Qb) σ.injective hne (horbit₁ σ) (horbit₂ σ)
  obtain ⟨s₀, hs₀⟩ :=
    (InfiniteGalois.mem_range_algebraMap_iff_fixed (k := ℚ) (x₁ + x₂)).mpr (fun σ => (hfix σ).1)
  obtain ⟨m₀, hm₀⟩ :=
    (InfiniteGalois.mem_range_algebraMap_iff_fixed (k := ℚ) (x₁ * x₂)).mpr (fun σ => (hfix σ).2)

  have hD₁ : (x₂ - ρ) * (4 * (x₁ - ρ) ^ 3 + 4 * α * (x₁ - ρ) + 4 * β)
      = (x₁ - ρ) ^ 4 - 2 * α * (x₁ - ρ) ^ 2 - 8 * β * (x₁ - ρ) + α ^ 2 := by
    rw [hΨeval, hΦeval] at R₁
    linear_combination R₁ - (x₂ * x₁ ^ 2) * hb₂K - (2 * x₂ * x₁ + x₁ ^ 2) * hb₄K
      - (x₂ + 2 * x₁) * hb₆K - hb₈K
  have hD₂ : (x₁ - ρ) * (4 * (x₂ - ρ) ^ 3 + 4 * α * (x₂ - ρ) + 4 * β)
      = (x₂ - ρ) ^ 4 - 2 * α * (x₂ - ρ) ^ 2 - 8 * β * (x₂ - ρ) + α ^ 2 := by
    rw [hΨeval, hΦeval] at R₂
    linear_combination R₂ - (x₁ * x₂ ^ 2) * hb₂K - (2 * x₁ * x₂ + x₂ ^ 2) * hb₄K
      - (x₁ + 2 * x₂) * hb₆K - hb₈K
  have hne' : x₁ - ρ ≠ x₂ - ρ := fun h => hne (sub_left_injective h)
  obtain ⟨hg₃, hg₄⟩ := duplicationClosed_of_swapped α β (x₁ - ρ) (x₂ - ρ) hne' hD₁ hD₂

  have hp : algebraMap ℚ Qb (-(s₀ - 2 * r)) = -((x₁ - ρ) + (x₂ - ρ)) := by
    simp only [map_neg, map_sub, map_mul, map_ofNat, hs₀, hρ]
    ring
  have hq : algebraMap ℚ Qb (m₀ - r * s₀ + r ^ 2) = (x₁ - ρ) * (x₂ - ρ) := by
    simp only [map_add, map_sub, map_mul, map_pow, hs₀, hm₀, hρ]
    ring
  refine ⟨-(s₀ - 2 * r), m₀ - r * s₀ + r ^ 2, ?_, ?_, ?_⟩
  ·
    intro h0
    apply hne'
    have hkey : algebraMap ℚ Qb ((-(s₀ - 2 * r)) ^ 2 - 4 * (m₀ - r * s₀ + r ^ 2))
        = ((x₁ - ρ) - (x₂ - ρ)) ^ 2 := by
      rw [map_sub, map_pow, map_mul, map_ofNat, hp, hq]
      ring
    rw [h0, _root_.map_zero] at hkey
    exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp hkey.symm)
  ·
    apply (algebraMap ℚ Qb).injective
    rw [_root_.map_zero]
    have hkey : algebraMap ℚ Qb (2 * A * -(s₀ - 2 * r) - 4 * B - (-(s₀ - 2 * r)) ^ 3
          + 6 * -(s₀ - 2 * r) * (m₀ - r * s₀ + r ^ 2))
        = 2 * α * -((x₁ - ρ) + (x₂ - ρ)) - 4 * β - (-((x₁ - ρ) + (x₂ - ρ))) ^ 3
          + 6 * -((x₁ - ρ) + (x₂ - ρ)) * ((x₁ - ρ) * (x₂ - ρ)) := by
      rw [map_add, map_sub, map_sub, map_pow, map_mul, map_mul, map_mul, map_mul, map_mul,
        map_ofNat, map_ofNat, map_ofNat, hp, hq, hα, hβ]
    rw [hkey]
    exact hg₃
  ·
    apply (algebraMap ℚ Qb).injective
    rw [_root_.map_zero]
    have hkey : algebraMap ℚ Qb (A ^ 2 - 2 * A * (m₀ - r * s₀ + r ^ 2)
          + 4 * B * -(s₀ - 2 * r) - (-(s₀ - 2 * r)) ^ 2 * (m₀ - r * s₀ + r ^ 2)
          + 5 * (m₀ - r * s₀ + r ^ 2) ^ 2)
        = α ^ 2 - 2 * α * ((x₁ - ρ) * (x₂ - ρ)) + 4 * β * -((x₁ - ρ) + (x₂ - ρ))
          - (-((x₁ - ρ) + (x₂ - ρ))) ^ 2 * ((x₁ - ρ) * (x₂ - ρ))
          + 5 * ((x₁ - ρ) * (x₂ - ρ)) ^ 2 := by
      rw [map_add, map_sub, map_add, map_sub, map_pow, map_mul, map_mul, map_mul, map_mul,
        map_mul, map_mul, map_pow, map_pow, map_ofNat, map_ofNat, map_ofNat, hp, hq, hα, hβ]
    rw [hkey]
    exact hg₄

end GaloisHalf

section Seam

theorem variableChange_Δ_ne_zero_of_ne_zero (C : VariableChange ℚ) (W : WeierstrassCurve ℚ)
    (hΔ : W.Δ ≠ 0) : (C • W).Δ ≠ 0 := by
  rw [variableChange_Δ]
  exact mul_ne_zero (pow_ne_zero 12 (Units.ne_zero _)) hΔ

theorem hauptmodulRelation_variableChange (C : VariableChange ℚ) (W : WeierstrassCurve ℚ)
    (g v : ℚ) (h : g * W.Δ = W.c₄ ^ 3 * v) :
    g * (C • W).Δ = (C • W).c₄ ^ 3 * v := by
  rw [variableChange_Δ, variableChange_c₄]
  linear_combination ((C.u⁻¹ : ℚˣ) : ℚ) ^ 12 * h

theorem hauptmodulRelation_of_variableChange (C : VariableChange ℚ) (W : WeierstrassCurve ℚ)
    (g v : ℚ) (h : g * (C • W).Δ = (C • W).c₄ ^ 3 * v) :
    g * W.Δ = W.c₄ ^ 3 * v := by
  have key := hauptmodulRelation_variableChange C⁻¹ (C • W) g v h
  rwa [inv_smul_smul] at key

end Seam

end M4cP4Five

theorem solution (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0) (h5 : ¬ W.ModRepIsIrreducible 5) :
    ∃ v : ℚ, v ≠ 0 ∧ (v ^ 2 + 10 * v + 5) ^ 3 * (W.Δ : ℚ) = (W.c₄ : ℚ) ^ 3 * v := by
  haveI : Invertible (2 : ℚ) := invertibleOfNonzero (by norm_num)
  haveI : Invertible (3 : ℚ) := invertibleOfNonzero (by norm_num)

  have hΔV : (W.map (Int.castRingHom ℚ)).Δ ≠ 0 := by
    rw [WeierstrassCurve.map_Δ, eq_intCast]
    exact Int.cast_ne_zero.mpr hΔ

  obtain ⟨p, q, hsep, hg₃, hg₄⟩ :=
    M4cP4Five.exists_rational_kernelQuadratic (W.map (Int.castRingHom ℚ)) hΔV h5

  have hΔ' : ((W.map (Int.castRingHom ℚ)).toShortNF • W.map (Int.castRingHom ℚ)).Δ ≠ 0 :=
    M4cP4Five.variableChange_Δ_ne_zero_of_ne_zero _ _ hΔV
  have hΔeq := Δ_of_isShortNF ((W.map (Int.castRingHom ℚ)).toShortNF • W.map (Int.castRingHom ℚ))
  have hc₄eq := c₄_of_isShortNF ((W.map (Int.castRingHom ℚ)).toShortNF • W.map (Int.castRingHom ℚ))
  have hAB : 4 * ((W.map (Int.castRingHom ℚ)).toShortNF • W.map (Int.castRingHom ℚ)).a₄ ^ 3
      + 27 * ((W.map (Int.castRingHom ℚ)).toShortNF • W.map (Int.castRingHom ℚ)).a₆ ^ 2 ≠ 0 := by
    intro h0
    exact hΔ' (by rw [hΔeq, h0, mul_zero])

  obtain ⟨v, hv, hrel⟩ := ModularCurve.exists_hauptmodulFive_of_kernelQuadratic _ _ p q hAB hsep hg₃ hg₄
  refine ⟨v, hv, ?_⟩

  have hrelV : (v ^ 2 + 10 * v + 5) ^ 3 * (W.map (Int.castRingHom ℚ)).Δ
      = (W.map (Int.castRingHom ℚ)).c₄ ^ 3 * v := by
    refine M4cP4Five.hauptmodulRelation_of_variableChange
      (W.map (Int.castRingHom ℚ)).toShortNF (W.map (Int.castRingHom ℚ)) _ v ?_
    rw [hΔeq, hc₄eq]
    linear_combination hrel
  rw [WeierstrassCurve.map_Δ, eq_intCast, WeierstrassCurve.map_c₄, eq_intCast] at hrelV
  exact hrelV

end S_WeierstrassCurve_exists_hauptmodulFive_of_not_modRepIsIrreducible
end P2MW
export P2MW.S_WeierstrassCurve_exists_hauptmodulFive_of_not_modRepIsIrreducible (solution)
