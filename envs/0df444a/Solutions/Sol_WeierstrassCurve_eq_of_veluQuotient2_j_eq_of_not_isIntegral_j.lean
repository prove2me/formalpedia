-- Prove2me | solution 1 for WeierstrassCurve.eq_of_veluQuotient2_j_eq_of_not_isIntegral_j
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/8253d783-033d-53b7-b9a4-36537fa058ed

import Mathlib
import Definitions.Def_WeierstrassCurve_Velu
import Definitions.Def_WeierstrassCurve_VeluOrderTwo
import Theorems.Thm_WeierstrassCurve_veluQuotient2_j
import Theorems.Thm_WeierstrassCurve_isElliptic_veluQuotient2_of_isElliptic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_eq_of_veluQuotient2_j_eq_of_not_isIntegral_j
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
p2m_attr_erase "instance" "WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4"
p2m_attr_erase "simp" "WeierstrassCurve.veluX_empty"

set_option autoImplicit false

open WeierstrassCurve WeierstrassCurve.Affine

set_option maxHeartbeats 160000000 in

theorem solution
    {F : Type*} [Field F] [CharZero F]
    (W : WeierstrassCurve F) [W.IsElliptic] (hj : ¬ _root_.IsIntegral ℤ W.j)
    {x₁ y₁ x₂ y₂ : F}
    (h₁ : W.toAffine.Equation x₁ y₁) (hg₁ : W.veluGy x₁ y₁ = 0)
    (h₂ : W.toAffine.Equation x₂ y₂) (hg₂ : W.veluGy x₂ y₂ = 0)
    (hΔ₁ : (W.veluQuotient2 x₁ y₁).Δ ≠ 0) (hΔ₂ : (W.veluQuotient2 x₂ y₂).Δ ≠ 0)
    (hjeq : @WeierstrassCurve.j F _ (W.veluQuotient2 x₁ y₁) ⟨isUnit_iff_ne_zero.mpr hΔ₁⟩ =
      @WeierstrassCurve.j F _ (W.veluQuotient2 x₂ y₂) ⟨isUnit_iff_ne_zero.mpr hΔ₂⟩) :
    x₁ = x₂ := by
  by_contra hne
  have hΔ0 : W.Δ ≠ 0 := W.isUnit_Δ.ne_zero

  have hy1 : y₁ = -(W.a₁ * x₁ + W.a₃) / 2 := by
    have h := hg₁
    simp only [WeierstrassCurve.veluGy] at h
    linear_combination (-1/2 : F) * h
  have hy2 : y₂ = -(W.a₁ * x₂ + W.a₃) / 2 := by
    have h := hg₂
    simp only [WeierstrassCurve.veluGy] at h
    linear_combination (-1/2 : F) * h

  have hΨ1 : 4 * x₁ ^ 3 + (W.a₁ ^ 2 + 4 * W.a₂) * x₁ ^ 2 + 2 * (2 * W.a₄ + W.a₁ * W.a₃) * x₁ +
      (W.a₃ ^ 2 + 4 * W.a₆) = 0 := by
    have h := (WeierstrassCurve.Affine.equation_iff x₁ y₁).mp h₁
    rw [hy1] at h
    linear_combination (-4 : F) * h
  have hΨ2 : 4 * x₂ ^ 3 + (W.a₁ ^ 2 + 4 * W.a₂) * x₂ ^ 2 + 2 * (2 * W.a₄ + W.a₁ * W.a₃) * x₂ +
      (W.a₃ ^ 2 + 4 * W.a₆) = 0 := by
    have h := (WeierstrassCurve.Affine.equation_iff x₂ y₂).mp h₂
    rw [hy2] at h
    linear_combination (-4 : F) * h

  set x₃ : F := -(W.a₁ ^ 2 + 4 * W.a₂) / 4 - x₁ - x₂ with hx3
  have ha2 : W.a₂ = -(x₁ + x₂ + x₃) - W.a₁ ^ 2 / 4 := by
    rw [hx3]; ring
  have ha4 : W.a₄ = (x₁ * x₂ + x₁ * x₃ + x₂ * x₃) - W.a₁ * W.a₃ / 2 := by
    have hsub : (x₁ - x₂) * (2 * W.a₄ + W.a₁ * W.a₃ - 2 * (x₁ * x₂ + x₁ * x₃ + x₂ * x₃)) = 0 := by
      rw [ha2] at hΨ1 hΨ2
      linear_combination (1/2 : F) * hΨ1 - (1/2 : F) * hΨ2
    have h := (mul_eq_zero.mp hsub).resolve_left (sub_ne_zero.mpr hne)
    linear_combination (1/2 : F) * h
  have ha6 : W.a₆ = -(x₁ * x₂ * x₃) - W.a₃ ^ 2 / 4 := by
    rw [ha2, ha4] at hΨ1
    linear_combination (1/4 : F) * hΨ1

  have hg1 : W.veluGx x₁ y₁ = (x₁ - x₂) * (x₁ - x₃) := by
    simp only [WeierstrassCurve.veluGx]; rw [hy1, ha2, ha4]; ring
  have hg2 : W.veluGx x₂ y₂ = (x₂ - x₁) * (x₂ - x₃) := by
    simp only [WeierstrassCurve.veluGx]; rw [hy2, ha2, ha4]; ring
  have hD1 : W.velu2QuadDisc x₁ = 16 * (x₂ - x₃) ^ 2 := by
    simp only [WeierstrassCurve.velu2QuadDisc, WeierstrassCurve.b₂, WeierstrassCurve.b₄]
    rw [ha2, ha4]; ring
  have hD2 : W.velu2QuadDisc x₂ = 16 * (x₁ - x₃) ^ 2 := by
    simp only [WeierstrassCurve.velu2QuadDisc, WeierstrassCurve.b₂, WeierstrassCurve.b₄]
    rw [ha2, ha4]; ring
  have hc4 : W.c₄ = 16 * (x₁^2 - x₁ * x₂ - x₁ * x₃ + x₂^2 - x₂ * x₃ + x₃^2) := by
    simp only [WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]
    rw [ha2, ha4]; ring
  have hc6 : W.c₆ = 32 * (x₁ - 2 * x₂ + x₃) * (x₁ + x₂ - 2 * x₃) * (2 * x₁ - x₂ - x₃) := by
    simp only [WeierstrassCurve.c₆, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆]
    rw [ha2, ha4, ha6]; ring
  have hΔ : W.Δ = 16 * ((x₁ - x₂) * (x₁ - x₃) * (x₂ - x₃)) ^ 2 := by
    simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
      WeierstrassCurve.b₈]
    rw [ha2, ha4, ha6]; ring

  have h12 : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hne
  have h21 : x₂ - x₁ ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  have h13 : x₁ - x₃ ≠ 0 := by
    intro h; apply hΔ0; rw [hΔ, h]; ring
  have h23 : x₂ - x₃ ≠ 0 := by
    intro h; apply hΔ0; rw [hΔ, h]; ring

  have jmul : W.j * W.Δ = W.c₄ ^ 3 := by
    rw [WeierstrassCurve.j, ← WeierstrassCurve.coe_Δ', mul_assoc, mul_comm (W.c₄ ^ 3), ← mul_assoc,
      Units.inv_mul, one_mul]

  have hj1 : @WeierstrassCurve.j F _ (W.veluQuotient2 x₁ y₁) ⟨isUnit_iff_ne_zero.mpr hΔ₁⟩ =
      (W.c₄ + 240 * W.veluGx x₁ y₁) ^ 3 / (W.veluGx x₁ y₁ * W.velu2QuadDisc x₁ ^ 2) :=
    WeierstrassCurve.veluQuotient2_j h₁ hg₁
  have hj2 : @WeierstrassCurve.j F _ (W.veluQuotient2 x₂ y₂) ⟨isUnit_iff_ne_zero.mpr hΔ₂⟩ =
      (W.c₄ + 240 * W.veluGx x₂ y₂) ^ 3 / (W.veluGx x₂ y₂ * W.velu2QuadDisc x₂ ^ 2) :=
    WeierstrassCurve.veluQuotient2_j h₂ hg₂
  rw [hj1, hj2, hc4, hg1, hg2, hD1, hD2] at hjeq
  rw [div_eq_div_iff
    (mul_ne_zero (mul_ne_zero h12 h13) (pow_ne_zero 2 (mul_ne_zero (by norm_num) (pow_ne_zero 2 h23))))
    (mul_ne_zero (mul_ne_zero h21 h23) (pow_ne_zero 2 (mul_ne_zero (by norm_num) (pow_ne_zero 2 h13))))] at hjeq

  have hprod : (x₁ - x₂) * (x₁ - x₃) * (x₂ - x₃) * (x₁ + x₂ - 2 * x₃) * (x₁^2 - x₁ * x₂ - x₁ * x₃ + x₂^2 - x₂ * x₃ + x₃^2) *
      (16 * x₁^2 - 31 * x₁ * x₂ - x₁ * x₃ + 16 * x₂^2 - x₂ * x₃ + x₃^2) * (256 * x₁^4 - 272 * x₁^3 * x₂ - 752 * x₁^3 * x₃ + 33 * x₁^2 * x₂^2 + 750 * x₁^2 * x₂ * x₃ + 753 * x₁^2 * x₃^2 - 272 * x₁ * x₂^3 + 750 * x₁ * x₂^2 * x₃ - 1500 * x₁ * x₂ * x₃^2 - 2 * x₁ * x₃^3 + 256 * x₂^4 - 752 * x₂^3 * x₃ + 753 * x₂^2 * x₃^2 - 2 * x₂ * x₃^3 + x₃^4) = 0 := by
    linear_combination (-(1 / 1048576) : F) * hjeq

  have hint : ∀ n : ℤ, _root_.IsIntegral ℤ ((n : ℤ) : F) := fun n => by
    simpa using (isIntegral_algebraMap (R := ℤ) (A := F) (x := n))

  rcases mul_eq_zero.mp hprod with h | hQ15
  · rcases mul_eq_zero.mp h with h | hQ7
    · rcases mul_eq_zero.mp h with h | hQ0
      · rcases mul_eq_zero.mp h with h | hL
        · rcases mul_eq_zero.mp h with h | h'
          · rcases mul_eq_zero.mp h with h' | h'
            · exact h12 h'
            · exact h13 h'
          · exact h23 h'
        ·
          have hc6' : W.c₆ = 0 := by rw [hc6, hL]; ring
          have hrel := W.c_relation
          have hj' : W.j = 1728 := by
            apply mul_right_cancel₀ hΔ0
            rw [jmul]
            linear_combination (-1 : F) * hrel + W.c₆ * hc6'
          exact hj (by rw [hj']; exact_mod_cast hint 1728)
      ·
        have hc4' : W.c₄ = 0 := by rw [hc4, hQ0]; ring
        have hj' : W.j = 0 := by
          apply mul_right_cancel₀ hΔ0
          rw [jmul, hc4']; ring
        exact hj (by rw [hj']; exact isIntegral_zero)
    ·
      have h9 : W.c₄ ^ 3 + 3375 * W.Δ = (16 * x₁^2 - 31 * x₁ * x₂ - x₁ * x₃ + 16 * x₂^2 - x₂ * x₃ + x₃^2) * (256 * x₁^4 - 272 * x₁^3 * x₂ - 752 * x₁^3 * x₃ + 4128 * x₁^2 * x₂^2 - 7440 * x₁^2 * x₂ * x₃ + 4848 * x₁^2 * x₃^2 - 272 * x₁ * x₂^3 - 7440 * x₁ * x₂^2 * x₃ + 14880 * x₁ * x₂ * x₃^2 - 8192 * x₁ * x₃^3 + 256 * x₂^4 - 752 * x₂^3 * x₃ + 4848 * x₂^2 * x₃^2 - 8192 * x₂ * x₃^3 + 4096 * x₃^4) := by
        rw [hc4, hΔ]; ring
      have hj' : W.j = -3375 := by
        apply mul_right_cancel₀ hΔ0
        rw [jmul]
        linear_combination h9 + (256 * x₁^4 - 272 * x₁^3 * x₂ - 752 * x₁^3 * x₃ + 4128 * x₁^2 * x₂^2 - 7440 * x₁^2 * x₂ * x₃ + 4848 * x₁^2 * x₃^2 - 272 * x₁ * x₂^3 - 7440 * x₁ * x₂^2 * x₃ + 14880 * x₁ * x₂ * x₃^2 - 8192 * x₁ * x₃^3 + 256 * x₂^4 - 752 * x₂^3 * x₃ + 4848 * x₂^2 * x₃^2 - 8192 * x₂ * x₃^3 + 4096 * x₃^4) * hQ7
      exact hj (by rw [hj']; exact_mod_cast hint (-3375))
  ·
    have h10 : W.c₄ ^ 6 + 191025 * W.c₄ ^ 3 * W.Δ - 121287375 * W.Δ ^ 2 =
        (256 * x₁^4 - 272 * x₁^3 * x₂ - 752 * x₁^3 * x₃ + 33 * x₁^2 * x₂^2 + 750 * x₁^2 * x₂ * x₃ + 753 * x₁^2 * x₃^2 - 272 * x₁ * x₂^3 + 750 * x₁ * x₂^2 * x₃ - 1500 * x₁ * x₂ * x₃^2 - 2 * x₁ * x₃^3 + 256 * x₂^4 - 752 * x₂^3 * x₃ + 753 * x₂^2 * x₃^2 - 2 * x₂ * x₃^3 + x₃^4) * (65536 * x₁^8 - 323584 * x₁^7 * x₂ - 200704 * x₁^7 * x₃ + 49926400 * x₁^6 * x₂^2 - 97587712 * x₁^6 * x₂ * x₃ + 49496320 * x₁^6 * x₃^2 - 194630656 * x₁^5 * x₂^3 + 284333568 * x₁^5 * x₂^2 * x₃ + 8429568 * x₁^5 * x₂ * x₃^2 - 101802496 * x₁^5 * x₃^3 + 306701824 * x₁^4 * x₂^4 - 253654016 * x₁^4 * x₂^3 * x₃ - 330352896 * x₁^4 * x₂^2 * x₃^2 + 206185984 * x₁^4 * x₂ * x₃^3 + 75706624 * x₁^4 * x₃^4 - 194630656 * x₁^3 * x₂^5 - 253654016 * x₁^3 * x₂^4 * x₃ + 1014616064 * x₁^3 * x₂^3 * x₃^2 - 574145536 * x₁^3 * x₂^2 * x₃^3 + 80886784 * x₁^3 * x₂ * x₃^4 - 76742656 * x₁^3 * x₃^5 + 49926400 * x₁^2 * x₂^6 + 284333568 * x₁^2 * x₂^5 * x₃ - 330352896 * x₁^2 * x₂^4 * x₃^2 - 574145536 * x₁^2 * x₂^3 * x₃^3 + 861218304 * x₁^2 * x₂^2 * x₃^4 - 393019392 * x₁^2 * x₂ * x₃^5 + 103874560 * x₁^2 * x₃^6 - 323584 * x₁ * x₂^7 - 97587712 * x₁ * x₂^6 * x₃ + 8429568 * x₁ * x₂^5 * x₃^2 + 206185984 * x₁ * x₂^4 * x₃^3 + 80886784 * x₁ * x₂^3 * x₃^4 - 393019392 * x₁ * x₂^2 * x₃^5 + 262012928 * x₁ * x₂ * x₃^6 - 67108864 * x₁ * x₃^7 + 65536 * x₂^8 - 200704 * x₂^7 * x₃ + 49496320 * x₂^6 * x₃^2 - 101802496 * x₂^5 * x₃^3 + 75706624 * x₂^4 * x₃^4 - 76742656 * x₂^3 * x₃^5 + 103874560 * x₂^2 * x₃^6 - 67108864 * x₂ * x₃^7 + 16777216 * x₃^8) := by
      rw [hc4, hΔ]; ring
    have key : W.Δ ^ 2 * (W.j ^ 2 + 191025 * W.j - 121287375) = 0 := by
      linear_combination h10 + (W.j * W.Δ + W.c₄ ^ 3) * jmul + 191025 * W.Δ * jmul +
        (65536 * x₁^8 - 323584 * x₁^7 * x₂ - 200704 * x₁^7 * x₃ + 49926400 * x₁^6 * x₂^2 - 97587712 * x₁^6 * x₂ * x₃ + 49496320 * x₁^6 * x₃^2 - 194630656 * x₁^5 * x₂^3 + 284333568 * x₁^5 * x₂^2 * x₃ + 8429568 * x₁^5 * x₂ * x₃^2 - 101802496 * x₁^5 * x₃^3 + 306701824 * x₁^4 * x₂^4 - 253654016 * x₁^4 * x₂^3 * x₃ - 330352896 * x₁^4 * x₂^2 * x₃^2 + 206185984 * x₁^4 * x₂ * x₃^3 + 75706624 * x₁^4 * x₃^4 - 194630656 * x₁^3 * x₂^5 - 253654016 * x₁^3 * x₂^4 * x₃ + 1014616064 * x₁^3 * x₂^3 * x₃^2 - 574145536 * x₁^3 * x₂^2 * x₃^3 + 80886784 * x₁^3 * x₂ * x₃^4 - 76742656 * x₁^3 * x₃^5 + 49926400 * x₁^2 * x₂^6 + 284333568 * x₁^2 * x₂^5 * x₃ - 330352896 * x₁^2 * x₂^4 * x₃^2 - 574145536 * x₁^2 * x₂^3 * x₃^3 + 861218304 * x₁^2 * x₂^2 * x₃^4 - 393019392 * x₁^2 * x₂ * x₃^5 + 103874560 * x₁^2 * x₃^6 - 323584 * x₁ * x₂^7 - 97587712 * x₁ * x₂^6 * x₃ + 8429568 * x₁ * x₂^5 * x₃^2 + 206185984 * x₁ * x₂^4 * x₃^3 + 80886784 * x₁ * x₂^3 * x₃^4 - 393019392 * x₁ * x₂^2 * x₃^5 + 262012928 * x₁ * x₂ * x₃^6 - 67108864 * x₁ * x₃^7 + 65536 * x₂^8 - 200704 * x₂^7 * x₃ + 49496320 * x₂^6 * x₃^2 - 101802496 * x₂^5 * x₃^3 + 75706624 * x₂^4 * x₃^4 - 76742656 * x₂^3 * x₃^5 + 103874560 * x₂^2 * x₃^6 - 67108864 * x₂ * x₃^7 + 16777216 * x₃^8) * hQ15
    have hq : W.j ^ 2 + 191025 * W.j - 121287375 = 0 :=
      (mul_eq_zero.mp key).resolve_left (pow_ne_zero 2 hΔ0)
    refine hj ⟨Polynomial.X ^ 2 + Polynomial.C (191025 : ℤ) * Polynomial.X - Polynomial.C (121287375 : ℤ),
      ?_, ?_⟩
    · monicity!
    · rw [Polynomial.eval₂_sub, Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
        Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_C, eq_intCast, eq_intCast]
      push_cast
      linear_combination hq

end S_WeierstrassCurve_eq_of_veluQuotient2_j_eq_of_not_isIntegral_j
end P2MW
export P2MW.S_WeierstrassCurve_eq_of_veluQuotient2_j_eq_of_not_isIntegral_j (solution)
