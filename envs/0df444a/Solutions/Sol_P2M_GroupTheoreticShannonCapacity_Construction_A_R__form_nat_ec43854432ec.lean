-- Prove2me | solution 1 for P2M_GroupTheoreticShannonCapacity_Construction_A_R__form_nat_ec43854432ec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:49:44.340489+00:00
-- url     : https://prove2.me/submissions/42d40f8a-ba44-4c38-9ed6-41ab7620b4cd

import Definitions.Def_GroupTheoreticShannonCapacity_P0Matrix
import Definitions.Def_GroupTheoreticShannonCapacity_MAlpha
import Definitions.Def_GroupTheoreticShannonCapacity_Construction
import Theorems.Thm_GroupTheoreticShannonCapacity_Construction_X_factorization
import Theorems.Thm_GroupTheoreticShannonCapacity_Construction_matrixA_eq_X_add_qI
import Theorems.Thm_P2M_GroupTheoreticShannonCapacity_Construction_diagPow_eq_D__e8c67f70ebf7
import Theorems.Thm_GroupTheoreticShannonCapacity_Construction_sR_sub_aI_isUnit
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
theorem _root_.solution (n k b r s : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) (hb : 1 ≤ b) (hs : 1 ≤ s)
    (hn_num : (s : ℤ) ^ n * (r : ℤ) + (k : ℤ) * (a n (k : ℤ) (b : ℤ) (r : ℤ) (s : ℤ)) ^ n ≠ 0) :
    let R := MAlpha.Rα n ((r : ℝ) / (k : ℝ))
    (matrixA n (k:ℤ) (b:ℤ) (r:ℤ) (s:ℤ)).map (↑· : ℚ → ℝ) =
    ((p n (k:ℤ) (b:ℤ) (r:ℤ) (s:ℤ) : ℝ) • R - (p n (k:ℤ) (b:ℤ) (r:ℤ) (s:ℤ) * (b:ℤ) : ℝ) • 1) *
    ((s : ℝ) • R - (a n (k:ℤ) (b:ℤ) (r:ℤ) (s:ℤ) : ℝ) • 1)⁻¹ := by
  intro R
  have hb_ne : (b : ℝ) ≠ 0 := by exact_mod_cast Nat.one_le_iff_ne_zero.mp hb
  have hk_ne : (k : ℝ) ≠ 0 := by exact_mod_cast Nat.one_le_iff_ne_zero.mp hk
  have hs_ne : (s : ℝ) ≠ 0 := by exact_mod_cast Nat.one_le_iff_ne_zero.mp hs
  -- a > 0 for natural parameters
  have ha_pos : (0 : ℝ) < (a n (k:ℤ) (b:ℤ) (r:ℤ) (s:ℤ) : ℝ) := by
    simp only [a]
    have hb_pos : 0 < (b : ℤ) := by omega
    have hk_pos : 0 < (k : ℤ) := by omega
    have hbn_pos : 0 < (b : ℤ) ^ n := pow_pos hb_pos n
    have h_kbn : 0 < (k : ℤ) * (b : ℤ) ^ n := mul_pos hk_pos hbn_pos
    have h_sb : 0 ≤ (s : ℤ) * (b : ℤ) := mul_nonneg (by omega) (by omega)
    have h_r : 0 ≤ (r : ℤ) := Int.natCast_nonneg r
    have h_sum : 0 < (k : ℤ) * (b : ℤ) ^ n + (s : ℤ) * (b : ℤ) + (r : ℤ) := by linarith
    exact_mod_cast h_sum
  have ha_ne : (a n (k:ℤ) (b:ℤ) (r:ℤ) (s:ℤ) : ℝ) ≠ 0 := ne_of_gt ha_pos
  have ha_inv_ne : (a n (k:ℤ) (b:ℤ) (r:ℤ) (s:ℤ) : ℝ)⁻¹ ≠ 0 := inv_ne_zero ha_ne
  set a' : ℝ := (a n (k:ℤ) (b:ℤ) (r:ℤ) (s:ℤ) : ℝ) with ha'_def
  -- β_X = rs^n / (ka^n) and we need β_X ≠ -1
  have hβ_X_def : (r : ℝ) * (s : ℝ)^n / ((k : ℝ) * a'^n) ≠ -1 := by
    have hdenom_pos : (0 : ℝ) < (k : ℝ) * a'^n := by positivity
    intro h
    rw [div_eq_iff (ne_of_gt hdenom_pos)] at h
    have hsum : (r : ℝ) * (s : ℝ)^n + (k : ℝ) * a'^n = 0 := by linarith
    -- But s^n * r + k * a^n ≠ 0
    have hne : (s : ℝ)^n * (r : ℝ) + (k : ℝ) * a'^n ≠ 0 := by
      simp only [ha'_def]
      have h' : (s : ℝ)^n * (r : ℝ) + (k : ℝ) * (a n (k:ℤ) (b:ℤ) (r:ℤ) (s:ℤ) : ℝ)^n =
          ((s : ℤ) ^ n * (r : ℤ) +
            (k : ℤ) * (a n (k:ℤ) (b:ℤ) (r:ℤ) (s:ℤ)) ^ n : ℤ) := by push_cast; ring
      rw [h']
      exact_mod_cast hn_num
    have heq : (r : ℝ) * (s : ℝ)^n = (s : ℝ)^n * (r : ℝ) := by ring
    rw [heq] at hsum
    exact hne hsum
  -- X_factorization gives X = scalar • (Dα * Mα * Dα⁻¹)
  have hX := X_factorization n k b r s hn hk hb (Nat.one_le_iff_ne_zero.mp hs)
  have hDiagInv : diagPow n ((s : ℝ)/a') = MAlpha.Dα n ((s : ℝ)/a') := diagPow_eq_Dα n ((s : ℝ)/a')
  have hDiag : diagPow n (a'/(s : ℝ)) = (MAlpha.Dα n ((s : ℝ)/a'))⁻¹ := by
    have h_sa_ne : (s : ℝ) / a' ≠ 0 := div_ne_zero hs_ne ha_ne
    rw [MAlpha.Dα_inv n ((s : ℝ)/a') h_sa_ne]
    have h_inv_inv : ((s : ℝ)/a')⁻¹ = a'/(s : ℝ) := by field_simp
    rw [h_inv_inv, diagPow_eq_Dα]
  -- Dα_Mα_conjugation gives the formula
  set α_X : ℝ := (r : ℝ) * (s : ℝ)^n / ((k : ℝ) * a'^n) with hα_X_def
  set β : ℝ := (s : ℝ) / a' with hβ_def
  have hβ_ne : β ≠ 0 := div_ne_zero hs_ne ha_ne
  have hMα_conj := MAlpha.Dα_Mα_conjugation n hn α_X β hβ_X_def hβ_ne
  -- γ = α_X * β^{-n} = r/k
  have hγ_eq : α_X * β⁻¹^n = (r : ℝ) / (k : ℝ) := by
    simp only [hα_X_def, hβ_def]
    have han_ne : a'^n ≠ 0 := pow_ne_zero _ ha_ne
    have hsn_ne : (s : ℝ)^n ≠ 0 := pow_ne_zero _ hs_ne
    rw [inv_pow, div_pow]
    field_simp [hk_ne, han_ne, hsn_ne, ha_ne]
  have hR_eq : MAlpha.Rα n (α_X * β⁻¹^n) = R := congrArg (MAlpha.Rα n) hγ_eq
  rw [hR_eq] at hMα_conj
  -- A = q•I + X, rewrite in terms of Dα
  have hA_expand : (matrixA n (k:ℤ) (b:ℤ) (r:ℤ) (s:ℤ)).map (↑· : ℚ → ℝ) =
      (q n (k:ℤ) (b:ℤ) (r:ℤ) (s:ℤ) : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ) +
      (matrixX n k b r s).map (↑· : ℚ → ℝ) := by
    rw [matrixA_eq_X_add_qI]
    rw [add_comm]
  -- X rewritten in terms of Dα
  have hX_rewrite : (matrixX n k b r s).map (↑· : ℚ → ℝ) =
      ((k : ℝ) * a'^(n-1) / (s : ℝ)) • (MAlpha.Dα n β * MAlpha.Mα n α_X *
        (MAlpha.Dα n β)⁻¹) := by
    rw [hX, hDiagInv, hDiag]
  rw [hA_expand, hX_rewrite, hMα_conj]
  -- Set up abbreviations
  set x_conj := (q n (k:ℤ) (b:ℤ) (r:ℤ) (s:ℤ) : ℝ) with hx_def
  set y_conj := (k : ℝ) * a'^(n-1) / (s : ℝ) with hy_def
  set A := β • R + α_X • (1 : Matrix (Fin n) (Fin n) ℝ) with hA_def
  set B := β • R - 1 with hB_def
  -- B is invertible
  have hB_det_ne : B.det ≠ 0 := by
    simp only [hB_def]
    have h := MAlpha.det_xRα_add_yI n hn β (-1) ((r : ℝ) / (k : ℝ))
    simp only [neg_one_smul] at h
    rw [sub_eq_add_neg, h]
    have hsimplify : (-β)^n * ((r : ℝ) / (k : ℝ)) + (-1)^n =
        (-1)^n * ((s : ℝ)^n * (r : ℝ) + (k : ℝ) * a'^n) / ((k : ℝ) * a'^n) := by
      simp only [hβ_def]
      rw [neg_pow ((s : ℝ)/a'), neg_pow 1, div_pow]
      have han_ne : a'^n ≠ 0 := pow_ne_zero _ ha_ne
      have hsn_ne : (s : ℝ)^n ≠ 0 := pow_ne_zero _ hs_ne
      field_simp [hk_ne, ha_ne, han_ne]
    rw [hsimplify]
    have hn_num_real : (s : ℝ)^n * (r : ℝ) + (k : ℝ) * a'^n ≠ 0 := by
      simp only [ha'_def]
      have h' : (s : ℝ)^n * (r : ℝ) + (k : ℝ) * (a n (k:ℤ) (b:ℤ) (r:ℤ) (s:ℤ) : ℝ)^n =
          ((s : ℤ) ^ n * (r : ℤ) +
            (k : ℤ) * (a n (k:ℤ) (b:ℤ) (r:ℤ) (s:ℤ)) ^ n : ℤ) := by push_cast; ring
      rw [h']
      exact_mod_cast hn_num
    have han_ne : a'^n ≠ 0 := pow_ne_zero _ ha_ne
    have hnum_ne : (-1 : ℝ)^n * ((s : ℝ)^n * (r : ℝ) + (k : ℝ) * a'^n) ≠ 0 :=
      mul_ne_zero (neg_one_pow_ne_zero n) hn_num_real
    exact div_ne_zero hnum_ne (mul_ne_zero hk_ne han_ne)
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
      (β * (x_conj + y_conj)) • R + (-x_conj + y_conj * α_X) • 1 := by
    simp only [hA_def, hB_def]
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply, smul_eq_mul]
    ring
  rw [hcoefs]
  -- Coefficient 1: β * (x_conj + y_conj) = p / a
  -- This is: (s/a)(q + ka^{n-1}/s) = p/a, which requires expanding p = qs + ka^{n-1}
  have h_coef1 : β * (x_conj + y_conj) = (p n (k:ℤ) (b:ℤ) (r:ℤ) (s:ℤ) : ℝ) / a' := by
    simp only [hx_def, hy_def, hβ_def, p, q, a]
    have hn_pos : 0 < n := by omega
    have hpow_eq : a'^n = a'^(n-1) * a' := by rw [← pow_succ]; congr 1; omega
    simp only [ha'_def, a]
    push_cast
    field_simp [hs_ne, ha_ne]
    -- The algebraic identity: s(s^{n-1}r + kb·a^{n-1}) + k(r+kb^n)·a^{n-1} = rs^n + k·a^n
    -- follows from a = kb^n + sb + r and expansion of a^n
    have ha_eq : (↑k * ↑b ^ n + ↑s * ↑b + ↑r : ℝ) = a' := by simp only [ha'_def, a]; push_cast; ring
    have hrk_eq : (↑r + ↑k * ↑b ^ n : ℝ) = a' - ↑s * ↑b := by linarith [ha_eq]
    have hs_pow : (↑s : ℝ) * ↑s ^ (n - 1) = ↑s ^ n := by
      rw [← pow_succ']
      congr 1
      omega
    rw [ha_eq, hrk_eq, hpow_eq, ← hs_pow]
    ring
  -- Coefficient 2: -x_conj + y_conj * α_X = -(p*b) / a
  -- This uses pb = qa - rs^{n-1} (from pb_eq_qa_minus theorem)
  have h_coef2 : -x_conj + y_conj * α_X = -(p n (k:ℤ) (b:ℤ) (r:ℤ) (s:ℤ) * (b:ℤ) : ℝ) / a' := by
    simp only [hx_def, hy_def, hα_X_def, p, q, a]
    have hn_pos : 0 < n := by omega
    have han_ne : a'^n ≠ 0 := pow_ne_zero _ ha_ne
    have hsn_ne : (s : ℝ)^n ≠ 0 := pow_ne_zero _ hs_ne
    have hpow_eq : a'^n = a'^(n-1) * a' := by rw [← pow_succ]; congr 1; omega
    simp only [ha'_def, a]
    push_cast
    field_simp [hs_ne, ha_ne, han_ne, hsn_ne]
    -- The algebraic identity follows from pb = qa - rs^{n-1}
    have ha_eq : (↑k * ↑b ^ n + ↑b * ↑s + ↑r : ℝ) = a' := by simp only [ha'_def, a]; push_cast; ring
    have hrk_eq : (↑r + ↑k * ↑b ^ n : ℝ) = a' - ↑b * ↑s := by linarith [ha_eq]
    have hs_pow : (↑s : ℝ) * ↑s ^ (n - 1) = ↑s ^ n := by
      rw [← pow_succ']
      congr 1
      omega
    rw [ha_eq, hrk_eq, hpow_eq, ← hs_pow]
    ring
  rw [h_coef1, h_coef2]
  -- Scale: numerator = (1/a) • (p•R - pb•I)
  have h_num : ((p n (k:ℤ) (b:ℤ) (r:ℤ) (s:ℤ) : ℝ) / a') • R +
      (-(p n (k:ℤ) (b:ℤ) (r:ℤ) (s:ℤ) * (b:ℤ) : ℝ) / a') • 1 =
      a'⁻¹ • ((p n (k:ℤ) (b:ℤ) (r:ℤ) (s:ℤ) : ℝ) • R -
        (p n (k:ℤ) (b:ℤ) (r:ℤ) (s:ℤ) * (b:ℤ) : ℝ) • 1) := by
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply, smul_eq_mul]
    field_simp [ha_ne]
    ring
  have h_denom : B = a'⁻¹ • ((s : ℝ) • R - a' • 1) := by
    simp only [hB_def, hβ_def]
    ext i j
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    by_cases h : i = j
    · simp only [h, ↓reduceIte, mul_one]; field_simp [ha_ne]
    · simp only [h, ↓reduceIte, mul_zero, sub_zero]; field_simp [ha_ne]
  rw [h_num, h_denom]
  -- (s•R - a•I) is invertible
  have hsR_sub_inv := sR_sub_aI_isUnit n k b r s hn hk hs hn_num
  have hsR_sub_det_unit := (Matrix.isUnit_iff_isUnit_det _).mp hsR_sub_inv
  -- Prove inverse scaling directly using left inverse
  have hsmul_inv : (a'⁻¹ • ((s : ℝ) • R - a' • 1))⁻¹ = a' • ((s : ℝ) • R - a' • 1)⁻¹ := by
    have hli : a' • ((s : ℝ) • R - a' • 1)⁻¹ * (a'⁻¹ • ((s : ℝ) • R - a' • 1)) = 1 := by
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ ha_ne, one_smul]
      exact Matrix.nonsing_inv_mul _ hsR_sub_det_unit
    exact Matrix.inv_eq_left_inv hli
  rw [hsmul_inv]
  rw [Matrix.smul_mul, ← Matrix.mul_smul, smul_smul, inv_mul_cancel₀ ha_ne, one_smul]
end GroupTheoreticShannonCapacity.Construction
