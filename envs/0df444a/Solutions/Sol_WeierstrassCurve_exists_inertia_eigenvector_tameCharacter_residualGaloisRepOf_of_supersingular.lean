-- Prove2me | solution 1 for WeierstrassCurve.exists_inertia_eigenvector_tameCharacter_residualGaloisRepOf_of_supersingular
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/290574c6-ea89-511c-8fd0-61da65d05ae6

import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Algebra.Algebra.ZMod
import Mathlib.Algebra.CharP.Lemmas
import Definitions.Def_GaloisRep_Residual
import Definitions.Def_GaloisRep_TameCharacter
import Theorems.Thm_WeierstrassCurve_valuation_torsion_of_coeff_prePsi_dvd
import Theorems.Thm_ValuationSubring_exists_units_mul_eq_and_residue_eq_tameCharacter_of_mem_inertiaSubgroupIn
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField
import Theorems.Thm_ValuationSubring_residueField_charP_of_liesOverPrime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_inertia_eigenvector_tameCharacter_residualGaloisRepOf_of_supersingular
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open Polynomial Matrix

namespace SSInertia

section groupLaw

variable {K : Type*} [Field K] {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ)

lemma bnd_mul {a b : K} {c d : Γ} (ha : v a * c ≤ 1) (hb : v b * d ≤ 1) :
    v (a * b) * (c * d) ≤ 1 := by
  rw [map_mul, mul_mul_mul_comm]
  exact mul_le_one' ha hb

lemma bnd_add {a b : K} {c : Γ} (ha : v a * c ≤ 1) (hb : v b * c ≤ 1) :
    v (a + b) * c ≤ 1 := by
  rcases le_total (v a) (v b) with h | h
  · exact le_trans (mul_le_mul' (v.map_add_le h le_rfl) le_rfl) hb
  · exact le_trans (mul_le_mul' (v.map_add_le le_rfl h) le_rfl) ha

lemma bnd_sub {a b : K} {c : Γ} (ha : v a * c ≤ 1) (hb : v b * c ≤ 1) :
    v (a - b) * c ≤ 1 := by
  rw [sub_eq_add_neg]
  exact bnd_add v ha (by rwa [Valuation.map_neg])

lemma bnd_neg {a : K} {c : Γ} (ha : v a * c ≤ 1) : v (-a) * c ≤ 1 := by
  rwa [Valuation.map_neg]

lemma bnd_weaken {a : K} {c d : Γ} (ha : v a * c ≤ 1) (hd : d ≤ 1) :
    v a * (c * d) ≤ 1 := by
  rw [← mul_assoc]; exact mul_le_one' ha hd

lemma bnd_const {a : K} (ha : v a ≤ 1) {d : Γ} (hd : d ≤ 1) : v a * d ≤ 1 :=
  mul_le_one' ha hd

variable [DecidableEq K] (W : WeierstrassCurve.Affine K)

theorem valuation_div_add_div_le (ha₁ : v W.a₁ ≤ 1) (ha₃ : v W.a₃ ≤ 1)
    {γ : Γ} (hγ1 : γ < 1) {x y y' : K}
    (hx : v x * γ ^ 2 = 1) (hy : v y * γ ^ 3 = 1) (hy' : v y' * γ ^ 3 = 1)
    (hsum : y + y' = -(W.a₁ * x + W.a₃)) :
    v (x / y + x / y') ≤ γ ^ 2 := by
  have hγpow : ∀ n : ℕ, γ ^ n ≤ 1 := fun n => pow_le_one₀ zero_le' hγ1.le
  have hx0 : x ≠ 0 := by intro h; rw [h, map_zero, zero_mul] at hx; exact zero_ne_one hx
  have hy0 : ∀ {y : K}, v y * γ ^ 3 = 1 → y ≠ 0 := by
    intro y hy h; rw [h, map_zero, zero_mul] at hy; exact zero_ne_one hy
  have hlin : v (W.a₁ * x + W.a₃) * γ ^ 2 ≤ 1 := by
    refine bnd_add v ?_ (bnd_const v ha₃ (hγpow 2))
    have := bnd_mul v (bnd_const v ha₁ (le_refl (1 : Γ))) hx.le
    rwa [one_mul] at this
  have hid : x / y + x / y' = -((x / y) * (x / y') * (W.a₁ * x + W.a₃) * x⁻¹) := by
    rw [show W.a₁ * x + W.a₃ = -(y + y') by rw [hsum]; ring]
    have := hy0 hy
    have := hy0 hy'
    field_simp
    ring
  have ht : ∀ {y : K}, v y * γ ^ 3 = 1 → v (x / y) = γ := by
    intro y hy
    have e : v (x / y) * v y = v x := by rw [← map_mul, div_mul_cancel₀ _ (hy0 hy)]
    calc v (x / y) = v (x / y) * (v y * γ ^ 3) := by rw [hy, mul_one]
      _ = v x * γ ^ 2 * γ := by rw [← mul_assoc, e, pow_succ, mul_assoc]
      _ = γ := by rw [hx, one_mul]
  have hu : v x⁻¹ = γ ^ 2 := by
    have e : v x⁻¹ * v x = 1 := by rw [← map_mul, inv_mul_cancel₀ hx0, map_one]
    calc v x⁻¹ = v x⁻¹ * (v x * γ ^ 2) := by rw [hx, mul_one]
      _ = γ ^ 2 := by rw [← mul_assoc, e, one_mul]
  rw [hid, Valuation.map_neg, map_mul, map_mul, map_mul, ht hy, ht hy', hu]
  calc γ * γ * v (W.a₁ * x + W.a₃) * γ ^ 2 = (v (W.a₁ * x + W.a₃) * γ ^ 2) * γ ^ 2 := by
        simp only [pow_two]; ac_rfl
    _ ≤ 1 * γ ^ 2 := mul_le_mul' hlin le_rfl
    _ = γ ^ 2 := one_mul _

theorem valuation_addX_div_addY_sub_le
    (ha₁ : v W.a₁ ≤ 1) (ha₂ : v W.a₂ ≤ 1) (ha₃ : v W.a₃ ≤ 1) (ha₄ : v W.a₄ ≤ 1) (ha₆ : v W.a₆ ≤ 1)
    {γ : Γ} (hγ0 : γ ≠ 0) (hγ1 : γ < 1)
    {x₁ x₂ y₁ y₂ : K} (h₁ : W.Equation x₁ y₁) (h₂ : W.Equation x₂ y₂)
    (hxy : ¬(x₁ = x₂ ∧ y₁ = W.negY x₂ y₂))
    (hx₁ : v x₁ * γ ^ 2 = 1) (hx₂ : v x₂ * γ ^ 2 = 1) (hy₁ : v y₁ * γ ^ 3 = 1)
    (hy₂ : v y₂ * γ ^ 3 = 1)
    (hx₃ : v (W.addX x₁ x₂ (W.slope x₁ x₂ y₁ y₂)) * γ ^ 2 = 1)
    (hy₃ : v (W.addY x₁ x₂ y₁ (W.slope x₁ x₂ y₁ y₂)) * γ ^ 3 = 1) :
    v (W.addX x₁ x₂ (W.slope x₁ x₂ y₁ y₂) / W.addY x₁ x₂ y₁ (W.slope x₁ x₂ y₁ y₂)
      - x₁ / y₁ - x₂ / y₂) ≤ γ ^ 2 := by

  set L := W.slope x₁ x₂ y₁ y₂ with hL
  set x₃ := W.addX x₁ x₂ L with hx₃def
  set y₃ := W.addY x₁ x₂ y₁ L with hy₃def
  have hγle : γ ≤ 1 := hγ1.le
  have hγpow : ∀ n : ℕ, γ ^ n ≤ 1 := fun n => pow_le_one₀ zero_le' hγle

  have hV := W.addPolynomial_slope h₁ h₂ hxy
  rw [WeierstrassCurve.Affine.addPolynomial_eq, neg_inj, Cubic.prod_X_sub_C_eq] at hV
  have e1 := Cubic.b_of_eq hV
  have e2 := Cubic.c_of_eq hV
  have e3 := Cubic.d_of_eq hV
  simp only [] at e1 e2 e3
  rw [← hL] at e1 e2 e3
  change _ = -(x₁ + x₂ + x₃) at e1
  change _ = x₁ * x₂ + x₁ * x₃ + x₂ * x₃ at e2
  change _ = -(x₁ * x₂ * x₃) at e3

  obtain ⟨μ, hμ⟩ : ∃ μ, μ = y₁ - L * x₁ := ⟨_, rfl⟩
  have hy1 : y₁ = L * x₁ + μ := by rw [hμ]; ring
  have hy2 : y₂ = L * x₂ + μ := by
    by_cases hx : x₁ = x₂
    · have hy : y₁ ≠ W.negY x₂ y₂ := fun h => hxy ⟨hx, h⟩
      rw [← WeierstrassCurve.Affine.Y_eq_of_Y_ne h₁ h₂ hx hy, ← hx, hy1]
    · have : L * (x₁ - x₂) = y₁ - y₂ := by
        rw [hL, WeierstrassCurve.Affine.slope_of_X_ne hx, div_mul_cancel₀ _ (sub_ne_zero.2 hx)]
      linear_combination this + hy1
  set yR := W.negAddY x₁ x₂ y₁ L with hyRdef
  have hyR : yR = L * x₃ + μ := by
    rw [hyRdef, WeierstrassCurve.Affine.negAddY, hμ]; ring
  have hy3R : y₃ = -yR - W.a₁ * x₃ - W.a₃ := by
    rw [hy₃def, WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negY]

  have hx0 : ∀ {x : K}, v x * γ ^ 2 = 1 → x ≠ 0 := by
    intro x hx h; rw [h, map_zero, zero_mul] at hx; exact zero_ne_one hx
  have hy0 : ∀ {y : K}, v y * γ ^ 3 = 1 → y ≠ 0 := by
    intro y hy h; rw [h, map_zero, zero_mul] at hy; exact zero_ne_one hy

  have hLb : v L * γ ^ 1 ≤ 1 := by
    rw [pow_one]
    by_contra hcon
    push Not at hcon
    have hbig : v W.a₁ < v L := by
      calc v W.a₁ ≤ 1 := ha₁
        _ < v L * γ := hcon
        _ ≤ v L * 1 := mul_le_mul' le_rfl hγle
        _ = v L := mul_one _
    have hsum : v (L * (L + W.a₁)) * γ ^ 2 ≤ 1 := by
      have : L * (L + W.a₁) = x₁ + x₂ + x₃ + W.a₂ := by linear_combination -e1
      rw [this]
      refine bnd_add v (bnd_add v (bnd_add v hx₁.le hx₂.le) hx₃.le) (bnd_const v ha₂ (hγpow 2))
    have : 1 < v (L * (L + W.a₁)) * γ ^ 2 := by
      rw [map_mul, v.map_add_eq_of_lt_left hbig, pow_two, mul_mul_mul_comm]
      exact one_lt_mul'' hcon hcon
    exact absurd hsum (not_le.2 this)
  have hμb : v μ * γ ^ 3 ≤ 1 := by
    rw [hμ]
    refine bnd_sub v hy₁.le ?_
    have := bnd_mul v hLb hx₁.le
    rwa [← pow_add] at this

  have hlin : v (W.a₁ * x₃ + W.a₃) * γ ^ 2 ≤ 1 := by
    refine bnd_add v ?_ (bnd_const v ha₃ (hγpow 2))
    have := bnd_mul v (bnd_const v ha₁ (le_refl (1 : Γ))) hx₃.le
    rwa [one_mul] at this
  have hyRv : v yR * γ ^ 3 = 1 := by
    have : yR = -(y₃ + (W.a₁ * x₃ + W.a₃)) := by rw [hy3R]; ring
    rw [this, Valuation.map_neg, v.map_add_eq_of_lt_left, hy₃]

    apply lt_of_mul_lt_mul_right' (a := γ ^ 3)
    rw [hy₃]
    calc v (W.a₁ * x₃ + W.a₃) * γ ^ 3 = v (W.a₁ * x₃ + W.a₃) * γ ^ 2 * γ := by
          rw [pow_succ, mul_assoc]
      _ ≤ 1 * γ := mul_le_mul' hlin le_rfl
      _ < 1 := by rw [one_mul]; exact hγ1

  set S : K := 3 * L ^ 2 * (x₁ * x₂ * x₃) + 2 * L * μ * (x₁ * x₂ + x₁ * x₃ + x₂ * x₃)
    + μ ^ 2 * (x₁ + x₂ + x₃) with hSdef
  have hSeq : S = W.a₃ * L ^ 2 * μ - 3 * W.a₆ * L ^ 2 + 2 * W.a₄ * L * μ - W.a₁ * L * μ ^ 2
      - W.a₂ * μ ^ 2 := by
    rw [hy1] at e2 e3
    rw [hSdef]
    linear_combination (3 * L ^ 2) * e3 - (2 * L * μ) * e2 + μ ^ 2 * e1
  have hSb : v S * γ ^ 7 ≤ 1 := by
    rw [hSeq]
    have hL2 : v (L ^ 2) * γ ^ 2 ≤ 1 := by
      have := bnd_mul v hLb hLb; rwa [← pow_two, ← pow_add] at this
    have hμ2 : v (μ ^ 2) * γ ^ 6 ≤ 1 := by
      have := bnd_mul v hμb hμb; rwa [← pow_two, ← pow_add] at this
    refine bnd_sub v (bnd_sub v (bnd_add v (bnd_sub v ?_ ?_) ?_) ?_) ?_
    ·
      have h := bnd_mul v (bnd_mul v (bnd_const v ha₃ (le_refl (1 : Γ))) hL2) hμb
      rw [one_mul, ← pow_add] at h
      have := bnd_weaken v h (hγpow 2)
      rwa [← pow_add] at this
    ·
      have h2 : v (2 : K) ≤ 1 := by
        simpa [one_add_one_eq_two] using v.map_add_le v.map_one.le v.map_one.le
      have h3 : v (3 : K) ≤ 1 := by
        simpa [show (2 : K) + 1 = 3 by norm_num] using v.map_add_le h2 v.map_one.le
      have h := bnd_mul v (bnd_mul v (bnd_const v h3 (le_refl (1 : Γ)))
        (bnd_const v ha₆ (le_refl (1 : Γ)))) hL2
      rw [one_mul, one_mul] at h
      have := bnd_weaken v h (hγpow 5)
      rwa [← pow_add] at this
    ·
      have h2 : v (2 : K) ≤ 1 := by
        simpa [one_add_one_eq_two] using v.map_add_le v.map_one.le v.map_one.le
      have h := bnd_mul v (bnd_mul v (bnd_mul v (bnd_const v h2 (le_refl (1 : Γ)))
        (bnd_const v ha₄ (le_refl (1 : Γ)))) hLb) hμb
      rw [one_mul, one_mul, ← pow_add] at h
      have := bnd_weaken v h (hγpow 3)
      rwa [← pow_add] at this
    ·
      have h := bnd_mul v (bnd_mul v (bnd_const v ha₁ (le_refl (1 : Γ))) hLb) hμ2
      rwa [one_mul, ← pow_add] at h
    ·
      have h := bnd_mul v (bnd_const v ha₂ (le_refl (1 : Γ))) hμ2
      rw [one_mul] at h
      have := bnd_weaken v h (hγpow 1)
      rwa [← pow_add] at this

  have hy10 : y₁ ≠ 0 := hy0 hy₁
  have hy20 : y₂ ≠ 0 := hy0 hy₂
  have hyR0 : yR ≠ 0 := hy0 hyRv
  have hy30 : y₃ ≠ 0 := hy0 hy₃
  have hx30 : x₃ ≠ 0 := hx0 hx₃
  have hT : (x₁ / y₁ + x₂ / y₂ + x₃ / yR) * (y₁ * y₂ * yR) = S := by
    rw [div_add_div _ _ hy10 hy20, div_add_div _ _ (mul_ne_zero hy10 hy20) hyR0,
      div_mul_cancel₀ _ (mul_ne_zero (mul_ne_zero hy10 hy20) hyR0), hSdef, hy1, hy2, hyR]
    rw [hy1] at hy10; rw [hy2] at hy20; rw [hyR] at hyR0
    ring
  have hTv : v (x₁ / y₁ + x₂ / y₂ + x₃ / yR) ≤ γ ^ 2 := by
    have hY : v (y₁ * y₂ * yR) * γ ^ 9 = 1 := by
      rw [map_mul, map_mul, show (9 : ℕ) = 3 + 3 + 3 from rfl, pow_add, pow_add]
      calc v y₁ * v y₂ * v yR * (γ ^ 3 * γ ^ 3 * γ ^ 3)
          = (v y₁ * γ ^ 3) * (v y₂ * γ ^ 3) * (v yR * γ ^ 3) := by ac_rfl
        _ = 1 := by rw [hy₁, hy₂, hyRv, one_mul, one_mul]
    calc v (x₁ / y₁ + x₂ / y₂ + x₃ / yR)
        = v (x₁ / y₁ + x₂ / y₂ + x₃ / yR) * (v (y₁ * y₂ * yR) * γ ^ 9) := by rw [hY, mul_one]
      _ = v S * γ ^ 7 * γ ^ 2 := by
          rw [← mul_assoc, ← map_mul, hT, show (9 : ℕ) = 7 + 2 from rfl, pow_add, mul_assoc]
      _ ≤ 1 * γ ^ 2 := mul_le_mul' hSb le_rfl
      _ = γ ^ 2 := one_mul _

  have hU : v (x₃ / y₃ + x₃ / yR) ≤ γ ^ 2 :=
    valuation_div_add_div_le v W ha₁ ha₃ hγ1 hx₃ hy₃ hyRv (by rw [hy3R]; ring)
  have : x₃ / y₃ - x₁ / y₁ - x₂ / y₂ = (x₃ / y₃ + x₃ / yR) - (x₁ / y₁ + x₂ / y₂ + x₃ / yR) := by
    ring
  rw [this]
  exact v.map_sub_le hU hTv

end groupLaw

section eigen

theorem exists_cast_eq_of_pow_eq_self {p : ℕ} [Fact p.Prime] {E : Type*} [Field E] [CharP E p]
    (r : E) (hr : r ^ p = r) : ∃ c : ZMod p, ZMod.castHom (dvd_refl p) E c = r := by
  classical
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  set f : E[X] := X ^ p - X with hf
  have hf0 : f ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero E hp1
  have hdeg : f.natDegree = p := FiniteField.X_pow_card_sub_X_natDegree_eq E hp1
  have hroot : ∀ y : E, y ∈ f.roots.toFinset ↔ y ^ p = y := by
    intro y
    rw [Multiset.mem_toFinset, mem_roots hf0, IsRoot, eval_sub, eval_pow, eval_X, sub_eq_zero]
  let S : Finset E := Finset.univ.image (ZMod.castHom (dvd_refl p) E)
  have hS : S ⊆ f.roots.toFinset := by
    intro y hy
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hy
    rw [hroot, ← map_pow, ZMod.pow_card]
  have hcardS : S.card = p := by
    rw [Finset.card_image_of_injective _ (ZMod.castHom_injective E), Finset.card_univ, ZMod.card]
  have hcardR : f.roots.toFinset.card ≤ p :=
    (Multiset.toFinset_card_le _).trans (hdeg ▸ Polynomial.card_roots' f)
  have hEq : S = f.roots.toFinset := Finset.eq_of_subset_of_card_le hS (by omega)
  have hr' : r ∈ f.roots.toFinset := (hroot r).2 hr
  rw [← hEq] at hr'
  obtain ⟨c, -, hc⟩ := Finset.mem_image.1 hr'
  exact ⟨c, hc⟩

theorem mulVec_eq_smul_of_additive_eigenfunctional {p : ℕ} [Fact p.Prime] {E : Type*} [Field E]
    [CharP E p] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    (x : Module.Basis (Fin 2) (ZMod p) V) (g : V →ₗ[ZMod p] V) (φ : V →+ E)
    (hφs : ∀ (c : ZMod p) (w : V), φ (c • w) = ZMod.castHom (dvd_refl p) E c * φ w)
    (hφi : ∀ w, φ w = 0 → w = 0) (θ : E) (hθ : ∀ w, φ (g w) = θ * φ w) :
    (![φ (x 1) ^ p, -φ (x 0) ^ p] : Fin 2 → E) ≠ 0 ∧
      ((LinearMap.toMatrix x x g).map (ZMod.castHom (dvd_refl p) E)) *ᵥ
          ![φ (x 1) ^ p, -φ (x 0) ^ p] = θ • ![φ (x 1) ^ p, -φ (x 0) ^ p] := by
  classical
  set c := ZMod.castHom (dvd_refl p) E with hc
  set a := LinearMap.toMatrix x x g with ha
  have hcp : ∀ z : ZMod p, c z ^ p = c z := fun z => by rw [← map_pow, ZMod.pow_card]

  have hφ0 : φ (x 0) ≠ 0 := fun h => x.ne_zero 0 (hφi _ h)
  have hφ1 : φ (x 1) ≠ 0 := fun h => x.ne_zero 1 (hφi _ h)

  have hcol : ∀ j, g (x j) = ∑ i, a i j • x i := fun j => by
    conv_lhs => rw [← Matrix.toLin_toMatrix x x g]
    rw [Matrix.toLin_self]
  have R : ∀ j, θ * φ (x j) = ∑ i, c (a i j) * φ (x i) := by
    intro j
    rw [← hθ, hcol, map_sum]
    simp only [hφs]
  have R0 := R 0
  have R1 := R 1
  simp only [Fin.sum_univ_two] at R0 R1

  have R0' : θ ^ p * φ (x 0) ^ p = c (a 0 0) * φ (x 0) ^ p + c (a 1 0) * φ (x 1) ^ p := by
    have := congrArg (· ^ p) R0
    simpa only [mul_pow, add_pow_char, hcp] using this
  have R1' : θ ^ p * φ (x 1) ^ p = c (a 0 1) * φ (x 0) ^ p + c (a 1 1) * φ (x 1) ^ p := by
    have := congrArg (· ^ p) R1
    simpa only [mul_pow, add_pow_char, hcp] using this

  have hδ : φ (x 0) * φ (x 1) ^ p - φ (x 1) * φ (x 0) ^ p ≠ 0 := by
    intro hδ
    have hq : (φ (x 1) / φ (x 0)) ^ p = φ (x 1) / φ (x 0) := by
      rw [div_pow, div_eq_div_iff (pow_ne_zero _ hφ0) hφ0]
      linear_combination hδ
    obtain ⟨d, hd⟩ := exists_cast_eq_of_pow_eq_self _ hq
    have h1 : φ (x 1 - d • x 0) = 0 := by
      rw [map_sub, hφs, hd, div_mul_cancel₀ _ hφ0, sub_self]
    have h2 := congrArg (fun w => x.repr w 1) (hφi _ h1)
    simp at h2

  refine ⟨fun h => ?_, ?_⟩
  · have := congrFun h 0
    simp only [Matrix.cons_val_zero, Pi.zero_apply] at this
    exact hφ1 (pow_eq_zero_iff (Fact.out : p.Prime).ne_zero |>.1 this)
  · ext i
    fin_cases i
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.map_apply]
      have key : (c (a 0 0) * φ (x 1) ^ p - c (a 0 1) * φ (x 0) ^ p - θ * φ (x 1) ^ p) *
          (φ (x 0) * φ (x 1) ^ p - φ (x 1) * φ (x 0) ^ p) = 0 := by
        linear_combination (-(φ (x 1) ^ p * φ (x 1) ^ p)) * R0 + (φ (x 0) ^ p * φ (x 1) ^ p) * R1
          + (φ (x 1) * φ (x 1) ^ p) * R0' - (φ (x 1) * φ (x 0) ^ p) * R1'
      have := (mul_eq_zero.1 key).resolve_right hδ
      linear_combination this
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.map_apply]
      have key : (c (a 1 0) * φ (x 1) ^ p - c (a 1 1) * φ (x 0) ^ p + θ * φ (x 0) ^ p) *
          (φ (x 0) * φ (x 1) ^ p - φ (x 1) * φ (x 0) ^ p) = 0 := by
        linear_combination (φ (x 1) ^ p * φ (x 0) ^ p) * R0 - (φ (x 0) ^ p * φ (x 0) ^ p) * R1
          - (φ (x 0) * φ (x 1) ^ p) * R0' + (φ (x 0) * φ (x 0) ^ p) * R1'
      have := (mul_eq_zero.1 key).resolve_right hδ
      linear_combination this

end eigen

section transport

theorem transport_eigenvector {p : ℕ} [Fact p.Prime] {k : Type} [Field k] (ι : ZMod p →+* k)
    (R : ResidualGaloisRep (ZMod p))
    (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* GL (Fin 2) k)
    (b : Module.Basis (Fin 2) k (R.baseChangeAlong ι).V)
    (hρ : ∀ σ, (ρ σ).val = LinearMap.toMatrix b b ((R.baseChangeAlong ι).ρ σ))
    {E : Type*} [Field E] (ψ : k →+* E)
    (x : Module.Basis (Fin 2) (ZMod p) R.V) (v : Fin 2 → E) (hv : v ≠ 0) :
    ∃ C : Matrix (Fin 2) (Fin 2) E, C *ᵥ v ≠ 0 ∧
      ∀ σ, (Matrix.GeneralLinearGroup.map ψ (ρ σ)).val *ᵥ (C *ᵥ v) =
        C *ᵥ (((LinearMap.toMatrix x x (R.ρ σ)).map (ψ.comp ι)) *ᵥ v) := by
  classical
  letI : Algebra (ZMod p) k := ι.toAlgebra
  let xk : Module.Basis (Fin 2) k (R.baseChangeAlong ι).V := Algebra.TensorProduct.basis k x
  have hxk : ∀ σ, LinearMap.toMatrix xk xk ((R.baseChangeAlong ι).ρ σ) =
      (LinearMap.toMatrix x x (R.ρ σ)).map ι := fun σ =>
    LinearMap.toMatrix_baseChange k (R.ρ σ) x x
  refine ⟨(b.toMatrix xk).map ψ, ?_, fun σ => ?_⟩
  · intro h
    apply hv
    have h1 : (xk.toMatrix b).map ψ * (b.toMatrix xk).map ψ = 1 := by
      rw [← Matrix.map_mul, Module.Basis.toMatrix_mul_toMatrix_flip,
        Matrix.map_one _ (map_zero ψ) (map_one ψ)]
    have := congrArg ((xk.toMatrix b).map ψ *ᵥ ·) h
    simpa only [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec, Matrix.mulVec_zero] using this
  · have hval : (Matrix.GeneralLinearGroup.map ψ (ρ σ)).val = (ρ σ).val.map ψ := rfl
    rw [hval, hρ σ, ← basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix b xk b xk, hxk,
      Matrix.map_mul, Matrix.map_mul, Matrix.map_map, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      Matrix.mul_assoc, ← Matrix.map_mul, Module.Basis.toMatrix_mul_toMatrix_flip,
      Matrix.map_one _ (map_zero ψ) (map_one ψ), Matrix.mul_one]
    rfl

end transport

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point IsLocalRing
open scoped WeierstrassCurve.Affine

section red
variable {K : Type*} [Field K] (A : ValuationSubring K)

noncomputable def red (z : K) : ResidueField A := by
  classical
  exact if h : z ∈ A then residue A ⟨z, h⟩ else 0

lemma red_of_mem {z : K} (h : z ∈ A) : red A z = residue A ⟨z, h⟩ := by
  classical
  exact dif_pos h

lemma red_zero : red A 0 = 0 := by
  rw [red_of_mem A A.zero_mem]; exact map_zero _

lemma red_add {a b : K} (ha : a ∈ A) (hb : b ∈ A) : red A (a + b) = red A a + red A b := by
  rw [red_of_mem A ha, red_of_mem A hb, red_of_mem A (A.add_mem _ _ ha hb), ← map_add]; rfl

lemma red_eq_zero_of_lt {a : K} (h : A.valuation a < 1) : red A a = 0 := by
  have ha : a ∈ A := (A.valuation_le_one_iff a).1 h.le
  rw [red_of_mem A ha, residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]
  exact h

lemma red_eq_of_sub {a b : K} (ha : a ∈ A) (hb : b ∈ A) (h : A.valuation (a - b) < 1) :
    red A a = red A b := by
  have : a = (a - b) + b := by ring
  rw [this, red_add A (sub_mem ha hb) hb, red_eq_zero_of_lt A h, zero_add]

lemma red_ne_zero_of_eq_one {a : K} (h : A.valuation a = 1) : red A a ≠ 0 := by
  have ha : a ∈ A := (A.valuation_le_one_iff a).1 h.le
  rw [red_of_mem A ha, Ne, residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]
  exact fun h' => (lt_irrefl _) (h ▸ h' : A.valuation a < A.valuation a)

end red

noncomputable def tPar {F : Type*} [Field F] {W : Affine F} : W.Point → F
  | .zero => 0
  | .some x y _ => x / y

@[scoped simp] lemma tPar_zero {F : Type*} [Field F] {W : Affine F} : tPar (0 : W.Point) = 0 := rfl
@[scoped simp] lemma tPar_some {F : Type*} [Field F] {W : Affine F} {x y : F} (h : W.Nonsingular x y) :
    tPar (Point.some x y h) = x / y := rfl

section curve

variable (W : WeierstrassCurve ℤ) (p : ℕ) [Fact p.Prime]

local notation "K" => AlgebraicClosure ℚ
local notation "E" => WeierstrassCurve.map W (Int.castRingHom ℚ)

lemma baseChange_a (A : ValuationSubring K) :
    A.valuation (E⁄K).a₁ ≤ 1 ∧ A.valuation (E⁄K).a₂ ≤ 1 ∧ A.valuation (E⁄K).a₃ ≤ 1 ∧
      A.valuation (E⁄K).a₄ ≤ 1 ∧ A.valuation (E⁄K).a₆ ≤ 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
  · rw [ValuationSubring.valuation_le_one_iff]
    simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
      WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆, eq_intCast,
      map_intCast]
    exact intCast_mem A _

variable (hp2 : p ≠ 2) (hgood : W.IsGoodPrimeFor p)
  (hss : ∀ i, 1 ≤ i → i < (p ^ 2 - 1) / 2 → (p : ℤ) ∣ (W.preΨ' p).coeff i)
  (A : ValuationSubring K) (hA : A.LiesOverPrime p) (π : K) (hπ : π ^ (p ^ 2 - 1) = p)

include hp2 hπ hA in
lemma gamma_facts : A.valuation π ≠ 0 ∧ A.valuation π < 1 ∧
    A.valuation (p : K) = (A.valuation π ^ 2) ^ ((p ^ 2 - 1) / 2) ∧ (p ^ 2 - 1) / 2 ≠ 0 := by
  have hp : p.Prime := Fact.out
  have heven : 2 * ((p ^ 2 - 1) / 2) = p ^ 2 - 1 :=
    Nat.two_mul_div_two_of_even (Nat.Odd.sub_odd (Odd.pow (hp.odd_of_ne_two hp2)) odd_one)
  have hm : (p ^ 2 - 1) / 2 ≠ 0 := by
    intro h
    have h3 : 3 ≤ p := by
      rcases hp.eq_two_or_odd' with h2 | hodd
      · exact absurd h2 hp2
      · have := hp.two_le; omega
    have : 9 ≤ p ^ 2 := by nlinarith
    omega
  have hvp : A.valuation (p : K) = (A.valuation π ^ 2) ^ ((p ^ 2 - 1) / 2) := by
    rw [← pow_mul, heven, ← map_pow, hπ]
  have hlt : A.valuation (p : K) < 1 := (ValuationSubring.mem_nonunits_iff A).1 hA
  refine ⟨?_, ?_, hvp, hm⟩
  · intro h0
    rw [Valuation.zero_iff] at h0
    rw [h0, zero_pow (by omega)] at hπ
    exact hp.ne_zero (by exact_mod_cast hπ.symm)
  · by_contra hge
    push Not at hge
    have : 1 ≤ A.valuation (p : K) := by
      rw [hvp]; exact one_le_pow₀ (one_le_pow₀ hge)
    exact absurd hlt (not_lt.2 this)

include hp2 hgood hss hA hπ in

lemma coord_val {x y : K} (h : (E⁄K).Nonsingular x y)
    (hP : (Point.some x y h : (E⁄K).Point) ∈ Submodule.torsionBy ℤ (E⁄K).Point p) :
    A.valuation x * A.valuation π ^ 2 = 1 ∧ A.valuation y * A.valuation π ^ 3 = 1 := by
  obtain ⟨hγ0, hγ1, hvp, hm⟩ := gamma_facts p hp2 A hA π hπ
  have hP' : p • (Point.some x y h : (E⁄K).Point) = 0 := by
    have := (Submodule.mem_torsionBy_iff _ _).1 hP
    rwa [Nat.cast_smul_eq_nsmul] at this
  obtain ⟨h1, h2⟩ := W.valuation_torsion_of_coeff_prePsi_dvd p hp2 hgood hss A hA x y h hP'
  have hx : A.valuation x * A.valuation π ^ 2 = 1 := by
    have : (A.valuation x * A.valuation π ^ 2) ^ ((p ^ 2 - 1) / 2) = 1 := by
      rw [mul_pow, ← hvp, h1]
    exact (pow_eq_one_iff.1 this).resolve_right hm
  refine ⟨hx, ?_⟩
  have : (A.valuation y * A.valuation π ^ 3) ^ 2 = 1 := by
    calc (A.valuation y * A.valuation π ^ 3) ^ 2 = A.valuation y ^ 2 * (A.valuation π ^ 2) ^ 3 := by
          rw [mul_pow, ← pow_mul, ← pow_mul]
      _ = (A.valuation x * A.valuation π ^ 2) ^ 3 := by rw [h2, mul_pow]
      _ = 1 := by rw [hx, one_pow]
  exact (pow_eq_one_iff.1 this).resolve_right two_ne_zero

include hp2 hgood hss hA hπ in

lemma tPar_val {x y : K} (h : (E⁄K).Nonsingular x y)
    (hP : (Point.some x y h : (E⁄K).Point) ∈ Submodule.torsionBy ℤ (E⁄K).Point p) :
    A.valuation (x / y / π) = 1 := by
  obtain ⟨hγ0, -, -, -⟩ := gamma_facts p hp2 A hA π hπ
  obtain ⟨hx, hy⟩ := coord_val W p hp2 hgood hss A hA π hπ h hP
  have hy0 : A.valuation y ≠ 0 := by intro h0; rw [h0, zero_mul] at hy; exact zero_ne_one hy
  rw [map_div₀, map_div₀, div_div, div_eq_one_iff_eq (mul_ne_zero hy0 hγ0)]
  calc A.valuation x = A.valuation x * (A.valuation y * A.valuation π ^ 3) := by rw [hy, mul_one]
    _ = A.valuation x * A.valuation π ^ 2 * (A.valuation y * A.valuation π) := by
        rw [pow_succ]; ac_rfl
    _ = A.valuation y * A.valuation π := by rw [hx, one_mul]

noncomputable def phi (Q : Submodule.torsionBy ℤ (E⁄K).Point p) : ResidueField A :=
  red A (tPar (Q : (E⁄K).Point) / π)

include hp2 hgood hss hA hπ in
lemma phi_ne_zero {Q : Submodule.torsionBy ℤ (E⁄K).Point p} (hQ : Q ≠ 0) :
    phi W p A π Q ≠ 0 := by
  obtain ⟨Q, hQmem⟩ := Q
  rcases Q with _ | ⟨x, y, h⟩
  · exact absurd rfl hQ
  · exact red_ne_zero_of_eq_one A (tPar_val W p hp2 hgood hss A hA π hπ h hQmem)

lemma phi_zero : phi W p A π 0 = 0 := by
  simp only [phi, Submodule.coe_zero, tPar_zero, zero_div, red_zero]

include hp2 hπ hA in
lemma val_div_pi_lt_one {z : K} (hz : A.valuation z ≤ A.valuation π ^ 2) :
    A.valuation (z / π) < 1 := by
  obtain ⟨hγ0, hγ1, -, -⟩ := gamma_facts p hp2 A hA π hπ
  have hπ0 : π ≠ 0 := fun h => hγ0 (by rw [h, Valuation.map_zero])
  have e : A.valuation (z / π) * A.valuation π = A.valuation z := by
    rw [← map_mul, div_mul_cancel₀ _ hπ0]
  apply lt_of_mul_lt_mul_right' (a := A.valuation π)
  rw [e, one_mul]
  calc A.valuation z ≤ A.valuation π ^ 2 := hz
    _ = A.valuation π * A.valuation π := pow_two _
    _ < 1 * A.valuation π := mul_lt_mul_of_pos_right hγ1 (zero_lt_iff.2 hγ0)
    _ = A.valuation π := one_mul _

include hp2 hgood hss hA hπ in

lemma phi_add (Q₁ Q₂ : Submodule.torsionBy ℤ (E⁄K).Point p) :
    phi W p A π (Q₁ + Q₂) = phi W p A π Q₁ + phi W p A π Q₂ := by
  obtain ⟨hγ0, hγ1, -, -⟩ := gamma_facts p hp2 A hA π hπ
  obtain ⟨ha₁, ha₂, ha₃, ha₄, ha₆⟩ := baseChange_a W A
  obtain ⟨P₁, hP₁⟩ := Q₁
  obtain ⟨P₂, hP₂⟩ := Q₂
  simp only [phi, Submodule.coe_add]
  rcases P₁ with _ | ⟨x₁, y₁, h₁⟩
  · change red A (tPar ((0 : (E⁄K).Point) + P₂) / π) =
      red A (tPar (0 : (E⁄K).Point) / π) + red A (tPar P₂ / π)
    rw [zero_add, tPar_zero, zero_div, red_zero, zero_add]
  rcases P₂ with _ | ⟨x₂, y₂, h₂⟩
  · change red A (tPar (Point.some x₁ y₁ h₁ + (0 : (E⁄K).Point)) / π) =
      red A (tPar (Point.some x₁ y₁ h₁) / π) + red A (tPar (0 : (E⁄K).Point) / π)
    rw [add_zero, tPar_zero, zero_div, red_zero, add_zero]
  obtain ⟨hx₁, hy₁⟩ := coord_val W p hp2 hgood hss A hA π hπ h₁ hP₁
  obtain ⟨hx₂, hy₂⟩ := coord_val W p hp2 hgood hss A hA π hπ h₂ hP₂
  have mem₁ : x₁ / y₁ / π ∈ A :=
    (A.valuation_le_one_iff _).1 (tPar_val W p hp2 hgood hss A hA π hπ h₁ hP₁).le
  have mem₂ : x₂ / y₂ / π ∈ A :=
    (A.valuation_le_one_iff _).1 (tPar_val W p hp2 hgood hss A hA π hπ h₂ hP₂).le
  by_cases hxy : x₁ = x₂ ∧ y₁ = (E⁄K).negY x₂ y₂
  · rw [add_of_Y_eq hxy.1 hxy.2, tPar_zero, zero_div, red_zero, tPar_some, tPar_some,
      ← red_add A mem₁ mem₂, eq_comm]
    apply red_eq_zero_of_lt
    have : x₁ / y₁ / π + x₂ / y₂ / π = (x₁ / y₁ + x₁ / y₂) / π := by rw [hxy.1]; ring
    rw [this]
    refine val_div_pi_lt_one p hp2 A hA π hπ ?_
    refine valuation_div_add_div_le A.valuation (E⁄K) ha₁ ha₃ hγ1 hx₁ hy₁ hy₂ ?_
    rw [hxy.2, hxy.1, WeierstrassCurve.Affine.negY]; ring
  · rw [add_some hxy, tPar_some, tPar_some, tPar_some, ← red_add A mem₁ mem₂]
    have hP₃ : (Point.some _ _ (nonsingular_add h₁ h₂ hxy) : (E⁄K).Point) ∈
        Submodule.torsionBy ℤ (E⁄K).Point p := by
      rw [← add_some (h₁ := h₁) (h₂ := h₂) hxy]; exact add_mem hP₁ hP₂
    obtain ⟨hx₃, hy₃⟩ := coord_val W p hp2 hgood hss A hA π hπ _ hP₃
    refine red_eq_of_sub A ((A.valuation_le_one_iff _).1
      (tPar_val W p hp2 hgood hss A hA π hπ _ hP₃).le) (add_mem mem₁ mem₂) ?_
    have : (E⁄K).addX x₁ x₂ ((E⁄K).slope x₁ x₂ y₁ y₂) /
          (E⁄K).addY x₁ x₂ y₁ ((E⁄K).slope x₁ x₂ y₁ y₂) / π - (x₁ / y₁ / π + x₂ / y₂ / π) =
        ((E⁄K).addX x₁ x₂ ((E⁄K).slope x₁ x₂ y₁ y₂) /
          (E⁄K).addY x₁ x₂ y₁ ((E⁄K).slope x₁ x₂ y₁ y₂) - x₁ / y₁ - x₂ / y₂) / π := by ring
    rw [this]
    exact val_div_pi_lt_one p hp2 A hA π hπ (valuation_addX_div_addY_sub_le A.valuation (E⁄K)
      ha₁ ha₂ ha₃ ha₄ ha₆ hγ0 hγ1 h₁.1 h₂.1 hxy hx₁ hx₂ hy₁ hy₂ hx₃ hy₃)

include hp2 hgood hss hA hπ in

lemma phi_smul {σ : K ≃ₐ[ℚ] K} (hσ : σ ∈ A.inertiaSubgroupIn ℚ)
    (Q : Submodule.torsionBy ℤ (E⁄K).Point p) :
    phi W p A π (σ • Q) = A.tameCharacter π σ * phi W p A π Q := by
  obtain ⟨hγ0, hγ1, -, -⟩ := gamma_facts p hp2 A hA π hπ
  have hπ0 : π ≠ 0 := fun h => hγ0 (by rw [h, Valuation.map_zero])
  obtain ⟨hK1, hK2⟩ :=
    ValuationSubring.exists_units_mul_eq_and_residue_eq_tameCharacter_of_mem_inertiaSubgroupIn A hσ
  obtain ⟨P, hP⟩ := Q
  change red A (tPar (σ • P) / π) = _ * red A (tPar P / π)
  rcases P with _ | ⟨x, y, h⟩
  · change red A (tPar (0 : (E⁄K).Point) / π) = _ * red A (tPar (0 : (E⁄K).Point) / π)
    rw [tPar_zero, zero_div, red_zero, mul_zero]
  · rw [algEquiv_smul_def, map_some, tPar_some, tPar_some]
    change red A (σ x / σ y / π) = _
    have hu : A.valuation (x / y / π) = 1 := tPar_val W p hp2 hgood hss A hA π hπ h hP
    set u : K := x / y / π with hudef
    have hu_mem : u ∈ A := (A.valuation_le_one_iff _).1 hu.le
    have hunit : IsUnit (⟨u, hu_mem⟩ : A) := (A.valuation_eq_one_iff _).2 hu
    obtain ⟨u', hu'⟩ := hunit
    have hu0 : u ≠ 0 := fun h0 => by rw [h0, Valuation.map_zero] at hu; exact zero_ne_one hu
    obtain ⟨aπ, haπ, hraπ⟩ := hK1 π hπ0
    obtain ⟨au, hau, hrau⟩ := hK1 u hu0
    have hone : A.tameCharacter u σ = 1 := by
      have := hK2 u'
      rwa [hu'] at this
    have key : σ x / σ y / π = ((au : A) : K) * ((aπ : A) : K) * u := by
      have hxy : x / y = u * π := by rw [hudef, div_mul_cancel₀ _ hπ0]
      rw [← map_div₀, hxy, map_mul, ← hau, ← haπ]
      field_simp
    have hmem : ((au : A) : K) * ((aπ : A) : K) * u ∈ A :=
      mul_mem (mul_mem (au : A).2 (aπ : A).2) hu_mem
    rw [key, red_of_mem A hmem, red_of_mem A hu_mem]
    have : (⟨((au : A) : K) * ((aπ : A) : K) * u, hmem⟩ : A) = (au : A) * (aπ : A) * ⟨u, hu_mem⟩ :=
      Subtype.ext rfl
    rw [this, map_mul, map_mul, hrau, hraπ, hone, one_mul]

noncomputable def phiHom : Submodule.torsionBy ℤ (E⁄K).Point p →+ ResidueField A where
  toFun := phi W p A π
  map_zero' := phi_zero W p A π
  map_add' := phi_add W p hp2 hgood hss A hA π hπ

@[scoped simp] lemma phiHom_apply (Q : Submodule.torsionBy ℤ (E⁄K).Point p) :
    phiHom W p hp2 hgood hss A hA π hπ Q = phi W p A π Q := rfl

end curve

end SSInertia
p2m_reactivate "P2MW.S_WeierstrassCurve_exists_inertia_eigenvector_tameCharacter_residualGaloisRepOf_of_supersingular.SSInertia"

open scoped WeierstrassCurve.Affine in
open SSInertia in
theorem solution
    (W : WeierstrassCurve ℤ) (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) {k : Type} [Field k] [Finite k]
    (ι : ZMod p →+* k) (hgood : W.IsGoodPrimeFor p)
    (hss : ∀ i, 1 ≤ i → i < (p ^ 2 - 1) / 2 → (p : ℤ) ∣ (W.preΨ' p).coeff i)
    (hcard : Nat.card (Submodule.torsionBy ℤ
      ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point p) = p ^ 2)
    (hker : GaloisFactorsThroughFiniteLevel
      (WeierstrassCurve.Affine.Point.galoisRepModuleEnd (K := AlgebraicClosure ℚ) ℚ
        (W.map (Int.castRingHom ℚ)) p))
    (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* GL (Fin 2) k)
    (b : Module.Basis (Fin 2) k
      (((W.map (Int.castRingHom ℚ)).residualGaloisRepOf p hcard hker).baseChangeAlong ι).V)
    (hρ : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (ρ σ).val =
      LinearMap.toMatrix b b
        ((((W.map (Int.castRingHom ℚ)).residualGaloisRepOf p hcard hker).baseChangeAlong ι).ρ σ))
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p)
    (π : AlgebraicClosure ℚ) (hπ : π ^ (p ^ 2 - 1) = p) :
    ∃ ψk : k →+* IsLocalRing.ResidueField P,
      ∃ v : Fin 2 → IsLocalRing.ResidueField P, v ≠ 0 ∧
        ((∀ σ ∈ P.inertiaSubgroupIn ℚ,
            (Matrix.GeneralLinearGroup.map ψk (ρ σ)).val.mulVec v = P.tameCharacter π σ • v) ∨
          (∀ σ ∈ P.inertiaSubgroupIn ℚ,
            (Matrix.GeneralLinearGroup.map ψk (ρ σ)).val.mulVec v = P.tameCharacter π σ ^ p • v)) := by
  have hp : p.Prime := Fact.out

  haveI : CharP (IsLocalRing.ResidueField P) p :=
    ValuationSubring.residueField_charP_of_liesOverPrime P hp hP
  haveI : IsAlgClosed (IsLocalRing.ResidueField P) := ValuationSubring.isAlgClosed_residueField P

  letI algk : Algebra (ZMod p) k := ι.toAlgebra
  letI algE : Algebra (ZMod p) (IsLocalRing.ResidueField P) := ZMod.algebra _ p
  haveI : Algebra.IsAlgebraic (ZMod p) k := Algebra.IsAlgebraic.of_finite (ZMod p) k
  let ψk : k →+* IsLocalRing.ResidueField P :=
    (IsAlgClosed.lift : k →ₐ[ZMod p] IsLocalRing.ResidueField P).toRingHom
  have hψι : ψk.comp ι = ZMod.castHom (dvd_refl p) (IsLocalRing.ResidueField P) :=
    RingHom.ext_zmod _ _

  let R := (W.map (Int.castRingHom ℚ)).residualGaloisRepOf p hcard hker
  let xB : Module.Basis (Fin 2) (ZMod p) R.V := Module.finBasisOfFinrankEq _ _ R.finrank_eq

  let φ : R.V →+ IsLocalRing.ResidueField P := phiHom W p hp2 hgood hss P hP π hπ
  have hφs : ∀ (c : ZMod p) (w : R.V),
      φ (c • w) = ZMod.castHom (dvd_refl p) (IsLocalRing.ResidueField P) c * φ w := by
    intro c w
    conv_lhs => rw [← ZMod.natCast_zmod_val c, Nat.cast_smul_eq_nsmul, map_nsmul, nsmul_eq_mul]
    rw [← ZMod.natCast_zmod_val c, map_natCast, ZMod.natCast_zmod_val]
  have hφi : ∀ w : R.V, φ w = 0 → w = 0 := fun w hw => by
    by_contra hne
    exact phi_ne_zero W p hp2 hgood hss P hP π hπ hne hw
  have hθ : ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ w : R.V,
      φ (R.ρ σ w) = P.tameCharacter π σ * φ w := fun σ hσ w =>
    phi_smul W p hp2 hgood hss P hP π hπ hσ w

  set vec : Fin 2 → IsLocalRing.ResidueField P := ![φ (xB 1) ^ p, -φ (xB 0) ^ p] with hvec
  have heig : ∀ σ ∈ P.inertiaSubgroupIn ℚ, vec ≠ 0 ∧
      ((LinearMap.toMatrix xB xB (R.ρ σ)).map
        (ZMod.castHom (dvd_refl p) (IsLocalRing.ResidueField P))) *ᵥ vec =
        P.tameCharacter π σ • vec := fun σ hσ =>
    mulVec_eq_smul_of_additive_eigenfunctional xB (R.ρ σ) φ hφs hφi _ (hθ σ hσ)
  have hvec0 : vec ≠ 0 := (heig 1 (Subgroup.one_mem _)).1

  obtain ⟨C, hC0, hC⟩ := transport_eigenvector ι R ρ b hρ ψk xB vec hvec0
  refine ⟨ψk, C *ᵥ vec, hC0, Or.inl fun σ hσ => ?_⟩
  rw [hC σ, hψι, (heig σ hσ).2, Matrix.mulVec_smul]

end S_WeierstrassCurve_exists_inertia_eigenvector_tameCharacter_residualGaloisRepOf_of_supersingular
end P2MW
export P2MW.S_WeierstrassCurve_exists_inertia_eigenvector_tameCharacter_residualGaloisRepOf_of_supersingular (solution)
