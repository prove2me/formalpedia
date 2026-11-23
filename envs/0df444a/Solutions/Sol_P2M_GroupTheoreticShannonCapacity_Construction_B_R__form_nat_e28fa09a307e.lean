-- Prove2me | solution 1 for P2M_GroupTheoreticShannonCapacity_Construction_B_R__form_nat_e28fa09a307e
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:49:40.332794+00:00
-- url     : https://prove2.me/submissions/5a2d87b6-67b6-4dfe-9053-fd8a1c220eba

import Definitions.Def_GroupTheoreticShannonCapacity_P0Matrix
import Definitions.Def_GroupTheoreticShannonCapacity_MAlpha
import Definitions.Def_GroupTheoreticShannonCapacity_Construction
import Theorems.Thm_GroupTheoreticShannonCapacity_Construction_Y_factorization
import Theorems.Thm_P2M_GroupTheoreticShannonCapacity_Construction_diagPow_eq_D__e8c67f70ebf7
import Theorems.Thm_GroupTheoreticShannonCapacity_Construction_R_sub_bI_isUnit
import Theorems.Thm_P2M_GroupTheoreticShannonCapacity_MAlpha_D__M__conjugation_a31a9f8e69a8
import Theorems.Thm_P2M_GroupTheoreticShannonCapacity_MAlpha_D__inv_5f24521fe641
import Theorems.Thm_P2M_GroupTheoreticShannonCapacity_MAlpha_det_xR__add_yI_9d0b1d30422b

section
namespace GroupTheoreticShannonCapacity.Construction
open Matrix
private lemma neg_one_pow_ne_zero (n : ℕ) : (-1 : ℝ)^n ≠ 0 := by
  rcases neg_one_pow_eq_or ℝ n with hp | hp <;> simp [hp]
section Tests
example : a 2 1 2 1 0 = 5 := by decide
example : p 2 1 2 1 0 = 5 := by
  simp only [p, a]
  norm_num
example : q 2 1 2 1 0 = 2 := by
  simp only [q, a]
  norm_num
example : p 2 1 2 1 0 = q 2 1 2 1 0 * 0 + 1 * (a 2 1 2 1 0)^(2-1) := by
  simp only [p, q, a]
  norm_num
example : p 2 1 2 1 0 * 2 = q 2 1 2 1 0 * (a 2 1 2 1 0) - 1 * 0^(2-1) := by
  simp only [p, q, a]
  norm_num
end Tests
end GroupTheoreticShannonCapacity.Construction
end

set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.Construction
open Matrix
namespace GroupTheoreticShannonCapacity.Construction
theorem _root_.solution (n k b r s : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) (hb : 1 ≤ b)
    (hd : (r : ℤ) + (k : ℤ) * (b : ℤ) ^ n ≠ 0) :
    let R := MAlpha.Rα n ((r : ℝ) / (k : ℝ))
    (matrixB n (k:ℤ) (b:ℤ) (r:ℤ) (s:ℤ)).map (↑· : ℚ → ℝ) =
    ((s : ℝ) • R - (a n (k:ℤ) (b:ℤ) (r:ℤ) (s:ℤ) : ℝ) • 1) *
    (R - (b : ℝ) • 1)⁻¹ := by
  intro R
  have hb_ne : (b : ℝ) ≠ 0 := by exact_mod_cast Nat.one_le_iff_ne_zero.mp hb
  have hk_ne : (k : ℝ) ≠ 0 := by exact_mod_cast Nat.one_le_iff_ne_zero.mp hk
  have hb_inv_ne : (b : ℝ)⁻¹ ≠ 0 := inv_ne_zero hb_ne
  have hn_pos : 0 < n := by omega
  have hpow_eq : (b : ℝ)^n = (b : ℝ)^(n-1) * (b : ℝ) := by rw [← pow_succ]; congr 1; omega
  -- β_Y ≠ -1
  have hβ_Y_def : (r : ℝ) / ((k : ℝ) * (b : ℝ)^n) ≠ -1 := by
    have hdenom_pos : (0 : ℝ) < (k : ℝ) * (b : ℝ)^n := by positivity
    intro h
    rw [div_eq_iff (ne_of_gt hdenom_pos)] at h
    have hsum : (r : ℝ) + (k : ℝ) * (b : ℝ)^n = 0 := by linarith
    exact (by exact_mod_cast hd : (r : ℝ) + (k : ℝ) * (b : ℝ)^n ≠ 0) hsum
  -- Y_factorization and Dα identities
  have hY := Y_factorization n k b r s hn hk hb
  have hDiagInv : diagPow n (b : ℝ)⁻¹ = MAlpha.Dα n (b : ℝ)⁻¹ := diagPow_eq_Dα n (b : ℝ)⁻¹
  have hDiag : diagPow n (b : ℝ) = (MAlpha.Dα n (b : ℝ)⁻¹)⁻¹ := by
    rw [MAlpha.Dα_inv n (b : ℝ)⁻¹ hb_inv_ne, inv_inv, diagPow_eq_Dα]
  -- Dα_Mα_conjugation gives the formula
  have hMα_conj := MAlpha.Dα_Mα_conjugation n hn ((r : ℝ) / ((k : ℝ) * (b : ℝ)^n)) (b : ℝ)⁻¹
    hβ_Y_def hb_inv_ne
  -- γ = β_Y * b^n = r/k
  have hγ_eq : (r : ℝ) / ((k : ℝ) * (b : ℝ)^n) * (b : ℝ)^n = (r : ℝ) / (k : ℝ) := by
    have hbn_ne : (b : ℝ)^n ≠ 0 := pow_ne_zero _ hb_ne
    field_simp [hk_ne, hbn_ne]
  have hR_eq : MAlpha.Rα n ((r : ℝ) / ((k : ℝ) * (b : ℝ)^n) * ((b : ℝ)⁻¹)⁻¹^n) = R := by
    simp only [inv_inv]
    exact congrArg (MAlpha.Rα n) hγ_eq
  rw [hR_eq] at hMα_conj
  -- Y rewritten in terms of Dα
  have hY_rewrite : (matrixY n (k:ℤ) (b:ℤ) (r:ℤ) (s:ℤ)).map (↑· : ℚ → ℝ) =
      (-(k : ℝ) * (b : ℝ)^(n-1)) •
        (MAlpha.Dα n (b : ℝ)⁻¹ * MAlpha.Mα n ((r : ℝ) / ((k : ℝ) * (b : ℝ)^n)) *
          (MAlpha.Dα n (b : ℝ)⁻¹)⁻¹) := by
    rw [hY, hDiagInv, hDiag]
  -- B = x_conj • I + Y
  have hB_expand : (matrixB n (k:ℤ) (b:ℤ) (r:ℤ) (s:ℤ)).map (↑· : ℚ → ℝ) =
      (((a n (k:ℤ) (b:ℤ) (r:ℤ) (s:ℤ) : ℝ) - (r : ℝ)) / (b : ℝ)) •
        (1 : Matrix (Fin n) (Fin n) ℝ) +
      (matrixY n (k:ℤ) (b:ℤ) (r:ℤ) (s:ℤ)).map (↑· : ℚ → ℝ) := by
    ext i j
    simp only [matrixB, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply]
    by_cases h : i = j
    · subst h
      simp only [↓reduceIte]
      simp only [zsmul_eq_mul, mul_one]
      have hdiv : (a n (k:ℤ) (b:ℤ) (r:ℤ) (s:ℤ) - (r : ℤ)) / (b : ℤ) =
          (k : ℤ) * (b : ℤ)^(n-1) + (s : ℤ) := by
        simp only [a]
        have hb_ne : (b : ℤ) ≠ 0 := by exact_mod_cast Nat.one_le_iff_ne_zero.mp hb
        have hn_pos : 0 < n := by omega
        have hpow : (b : ℤ)^n = (b : ℤ)^(n-1) * (b : ℤ) := by
          rw [← pow_succ]; congr 1; omega
        rw [hpow]
        have heq : (k : ℤ) * ((b : ℤ)^(n-1) * (b : ℤ)) + (s : ℤ) * (b : ℤ) + (r : ℤ) - (r : ℤ) =
            (b : ℤ) * ((k : ℤ) * (b : ℤ)^(n-1) + (s : ℤ)) := by ring
        rw [heq, Int.mul_ediv_cancel_left _ hb_ne]
      simp only [hdiv, smul_eq_mul, mul_one]
      push_cast
      simp only [a]
      field_simp [hb_ne]
      push_cast
      rw [hpow_eq]
      ring
    · simp only [h, ↓reduceIte, smul_eq_mul, mul_zero, smul_zero, zero_add]
  rw [hB_expand, hY_rewrite, hMα_conj]
  -- Set up abbreviations
  set x_conj := ((a n (k:ℤ) (b:ℤ) (r:ℤ) (s:ℤ) : ℝ) - (r : ℝ)) / (b : ℝ) with hx_def
  set y_conj := -(k : ℝ) * (b : ℝ)^(n-1) with hy_def
  set β_Y := (r : ℝ) / ((k : ℝ) * (b : ℝ)^n) with hβ_def
  set A := (b : ℝ)⁻¹ • R + β_Y • (1 : Matrix (Fin n) (Fin n) ℝ) with hA_def
  set B := (b : ℝ)⁻¹ • R - 1 with hB_def
  -- B is invertible
  have hB_det_ne : B.det ≠ 0 := by
    simp only [hB_def]
    have h := MAlpha.det_xRα_add_yI n hn (b : ℝ)⁻¹ (-1) ((r : ℝ) / (k : ℝ))
    simp only [neg_one_smul] at h
    rw [sub_eq_add_neg, h]
    have hsimplify : (-(b : ℝ)⁻¹)^n * ((r : ℝ) / (k : ℝ)) + (-1)^n =
        (-1)^n * ((r : ℝ) + (k : ℝ) * (b : ℝ)^n) / ((k : ℝ) * (b : ℝ)^n) := by
      rw [neg_pow (b : ℝ)⁻¹, neg_pow 1, inv_pow]
      field_simp [hk_ne, hb_ne]
    rw [hsimplify]
    have hd_real : (r : ℝ) + (k : ℝ) * (b : ℝ)^n ≠ 0 := by exact_mod_cast hd
    have hbn_ne : (b : ℝ)^n ≠ 0 := pow_ne_zero _ hb_ne
    have hnum_ne : (-1 : ℝ)^n * ((r : ℝ) + (k : ℝ) * (b : ℝ)^n) ≠ 0 :=
      mul_ne_zero (neg_one_pow_ne_zero n) hd_real
    exact div_ne_zero hnum_ne (mul_ne_zero hk_ne hbn_ne)
  have hB_unit : IsUnit B.det := isUnit_iff_ne_zero.mpr hB_det_ne
  -- x • I + y • (A * B⁻¹) = (x • B + y • A) * B⁻¹
  have hkey : x_conj • (1 : Matrix (Fin n) (Fin n) ℝ) + y_conj • (A * B⁻¹) =
      (x_conj • B + y_conj • A) * B⁻¹ := by
    calc x_conj • (1 : Matrix (Fin n) (Fin n) ℝ) + y_conj • (A * B⁻¹)
        = x_conj • (B * B⁻¹) + y_conj • (A * B⁻¹) := by rw [Matrix.mul_nonsing_inv B hB_unit]
      _ = (x_conj • B) * B⁻¹ + (y_conj • A) * B⁻¹ := by simp only [Matrix.smul_mul]
      _ = (x_conj • B + y_conj • A) * B⁻¹ := by rw [← Matrix.add_mul]
  rw [hkey]
  -- Simplify x_conj • B + y_conj • A
  have hcoefs : x_conj • B + y_conj • A =
      ((b : ℝ)⁻¹ * (x_conj + y_conj)) • R + (-x_conj + y_conj * β_Y) • 1 := by
    simp only [hA_def, hB_def]
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply, smul_eq_mul]
    ring
  rw [hcoefs]
  -- Coefficient 1: b⁻¹ * (x_conj + y_conj) = s * b⁻¹
  have h_coef1 : (b : ℝ)⁻¹ * (x_conj + y_conj) = (s : ℝ) * (b : ℝ)⁻¹ := by
    simp only [hx_def, hy_def, a]
    push_cast; field_simp [hb_ne]; rw [hpow_eq]; ring
  -- Coefficient 2: -x_conj + y_conj * β_Y = -a * b⁻¹
  have h_coef2 : -x_conj + y_conj * β_Y = -(a n (k:ℤ) (b:ℤ) (r:ℤ) (s:ℤ) : ℝ) * (b : ℝ)⁻¹ := by
    simp only [hx_def, hy_def, hβ_def]
    have hbn_ne : (b : ℝ)^n ≠ 0 := pow_ne_zero _ hb_ne
    field_simp [hb_ne, hk_ne, hbn_ne]; rw [hpow_eq]; ring
  rw [h_coef1, h_coef2]
  -- Scale: (c•A) * (c•B)⁻¹ = A * B⁻¹
  have h_num : ((s : ℝ) * (b : ℝ)⁻¹) • R + (-(a n (k:ℤ) (b:ℤ) (r:ℤ) (s:ℤ) : ℝ) * (b : ℝ)⁻¹) • 1 =
      (b : ℝ)⁻¹ • ((s : ℝ) • R - (a n (k:ℤ) (b:ℤ) (r:ℤ) (s:ℤ) : ℝ) • 1) := by
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply, smul_eq_mul]
    ring
  have h_denom : B = (b : ℝ)⁻¹ • (R - (b : ℝ) • 1) := by
    simp only [hB_def]
    ext i j
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    by_cases h : i = j
    · simp only [h, ↓reduceIte, mul_one]; field_simp [hb_ne]
    · simp only [h, ↓reduceIte, mul_zero, sub_zero]
  rw [h_num, h_denom]
  -- R - b • I is invertible
  have hR_sub_inv := R_sub_bI_isUnit n k b r hn hk hd
  have hR_sub_det_unit := (Matrix.isUnit_iff_isUnit_det _).mp hR_sub_inv
  -- Prove inverse scaling directly using left inverse
  have hsmul_inv : ((b : ℝ)⁻¹ • (R - (b : ℝ) • 1))⁻¹ = (b : ℝ) • (R - (b : ℝ) • 1)⁻¹ := by
    have hli : (b : ℝ) • (R - (b : ℝ) • 1)⁻¹ * ((b : ℝ)⁻¹ • (R - (b : ℝ) • 1)) = 1 := by
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hb_ne, one_smul]
      exact Matrix.nonsing_inv_mul _ hR_sub_det_unit
    exact Matrix.inv_eq_left_inv hli
  rw [hsmul_inv]
  rw [Matrix.smul_mul, ← Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hb_ne, one_smul]
end GroupTheoreticShannonCapacity.Construction
