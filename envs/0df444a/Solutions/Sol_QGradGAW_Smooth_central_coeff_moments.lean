-- Prove2me | solution 1 for QGradGAW.Smooth.central_coeff_moments
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T17:16:13.603885+00:00
-- url     : https://prove2.me/submissions/05a2f8ca-bbdc-4fc4-8b04-1d7139efd19d

import Mathlib
import Definitions.Def_QGradGAW_Smooth_Setting

set_option autoImplicit false
open QGradGAW.Smooth
open scoped fwdDiff

lemma qg_zpow_parity (i m : ℕ) : (-1:ℝ)^((i:ℤ)-m-1) = (-1)^(i+m+1) := by
  have h : ((i:ℤ)-m-1) = ((i+m+1 : ℕ):ℤ) + 2*(-((m:ℤ)+1)) := by push_cast; ring
  rw [h, zpow_add₀ (by norm_num), zpow_natCast, zpow_mul]
  norm_num

lemma qg_ratio (m a : ℕ) (ha : a ≤ m) :
    (m.choose a : ℝ) / ((m+a).choose a : ℝ) =
      ((m.factorial:ℝ))^2 / (((m-a).factorial : ℝ) * ((m+a).factorial : ℝ)) := by
  rw [Nat.cast_choose ℝ ha, Nat.cast_choose ℝ (Nat.le_add_left a m)]
  have : m + a - a = m := by omega
  rw [this]
  have h1 : (a.factorial:ℝ) ≠ 0 := by positivity
  have h2 : ((m-a).factorial:ℝ) ≠ 0 := by positivity
  have h3 : ((m+a).factorial:ℝ) ≠ 0 := by positivity
  have h4 : (m.factorial:ℝ) ≠ 0 := by positivity
  field_simp

lemma qg_ratio2 (m i : ℕ) (hi : i ≤ 2*m) :
    ((2*m).choose i : ℝ) / ((2*m).choose m : ℝ) =
      (m.factorial:ℝ)^2 / ((i.factorial:ℝ) * ((2*m-i).factorial:ℝ)) := by
  have hm : m ≤ 2*m := by omega
  rw [Nat.cast_choose ℝ hi, Nat.cast_choose ℝ hm]
  have : 2*m - m = m := by omega
  rw [this]
  have h1 : (i.factorial:ℝ) ≠ 0 := by positivity
  have h2 : ((2*m-i).factorial:ℝ) ≠ 0 := by positivity
  have h3 : ((2*m).factorial:ℝ) ≠ 0 := by positivity
  have h4 : (m.factorial:ℝ) ≠ 0 := by positivity
  field_simp

lemma qg_key (m i : ℕ) (hi : i ≤ 2*m) :
    centralCoeff m ((i:ℤ)-m) * (((i:ℤ)-m : ℤ) : ℝ) =
      (-1:ℝ)^(i+m+1) * (((2*m).choose i : ℝ) / ((2*m).choose m : ℝ)) + (if i = m then 1 else 0) := by
  by_cases him : i = m
  · subst him
    have hc : ((2*i).choose i : ℝ) ≠ 0 := by
      have : 0 < (2*i).choose i := Nat.choose_pos (by omega)
      positivity
    simp [centralCoeff, hc]
  · have hne : ((i:ℤ)-m) ≠ 0 := by omega
    simp only [centralCoeff, if_neg hne, if_neg him, add_zero]
    rw [qg_ratio2 m i hi, qg_zpow_parity]
    have hℓ : (((i:ℤ)-m : ℤ) : ℝ) ≠ 0 := by exact_mod_cast hne
    rcases lt_or_gt_of_ne him with h | h
    · have ha : ((i:ℤ)-m).natAbs = m - i := by omega
      rw [ha, qg_ratio m (m-i) (by omega)]
      have e1 : m - (m - i) = i := by omega
      have e2 : m + (m - i) = 2*m - i := by omega
      rw [e1, e2]
      field_simp
    · have ha : ((i:ℤ)-m).natAbs = i - m := by omega
      rw [ha, qg_ratio m (i-m) (by omega)]
      have e1 : m - (i - m) = 2*m - i := by omega
      have e2 : m + (i - m) = i := by omega
      rw [e1, e2]
      field_simp

lemma qg_fd_zero (m j : ℕ) (hj : j < 2*m) :
    ∑ i ∈ Finset.range (2*m+1), (-1:ℝ)^(i) * ((2*m).choose i : ℝ) * ((i:ℝ) - m)^j = 0 := by
  have h := fwdDiff_iter_pow_eq_zero_of_lt (R := ℝ) hj
  have h2 := fwdDiff_iter_comp_add (h := (1:ℝ)) (fun r : ℝ => r^j) (-(m:ℝ)) (2*m) 0
  rw [h] at h2
  rw [fwdDiff_iter_eq_sum_shift] at h2
  simp only [Pi.zero_apply] at h2
  rw [← h2]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i ≤ 2*m := by simp at hi; omega
  have hs : (-1:ℝ)^(2*m-i) = (-1)^i := by
    have e : (-1:ℝ)^(2*m-i) * (-1)^i = 1 := by
      rw [← pow_add, Nat.sub_add_cancel hi', pow_mul]; norm_num
    have e2 : ((-1:ℝ)^i)^2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    calc (-1:ℝ)^(2*m-i) = (-1)^(2*m-i) * ((-1)^i * (-1)^i) := by
          rw [← sq, e2]; ring
      _ = ((-1:ℝ)^(2*m-i) * (-1)^i) * (-1)^i := by ring
      _ = (-1)^i := by rw [e]; ring
  simp [zsmul_eq_mul, hs, sub_eq_add_neg]

lemma qg_cc_neg (m : ℕ) (ℓ : ℤ) : centralCoeff m (-ℓ) = - centralCoeff m ℓ := by
  by_cases h : ℓ = 0
  · subst h; simp [centralCoeff]
  · have h' : -ℓ ≠ 0 := neg_ne_zero.mpr h
    simp only [centralCoeff, if_neg h, if_neg h', Int.natAbs_neg]
    have : (-1:ℝ)^(-ℓ-1) = (-1)^(ℓ-1) := by
      have e : (-ℓ-1) = (ℓ-1) + 2*(-ℓ) := by ring
      rw [e, zpow_add₀ (by norm_num), zpow_mul]
      norm_num
    rw [this]
    push_cast
    rw [div_neg]
    ring

lemma qg_sum_odd (m : ℕ) (F : ℤ → ℝ) (hF : ∀ ℓ, F (-ℓ) = - F ℓ) :
    ∑ ℓ ∈ Finset.Icc (-(m:ℤ)) m, F ℓ = 0 := by
  have h : ∑ ℓ ∈ Finset.Icc (-(m:ℤ)) m, F ℓ = ∑ ℓ ∈ Finset.Icc (-(m:ℤ)) m, F (-ℓ) := by
    apply Finset.sum_nbij' (fun ℓ => -ℓ) (fun ℓ => -ℓ)
    · intro a ha; simp only [Finset.mem_Icc] at *; omega
    · intro a ha; simp only [Finset.mem_Icc] at *; omega
    · intro a _; simp
    · intro a _; simp
    · intro a _; simp
  have h2 : ∑ ℓ ∈ Finset.Icc (-(m:ℤ)) m, F (-ℓ) = - ∑ ℓ ∈ Finset.Icc (-(m:ℤ)) m, F ℓ := by
    simp [hF, Finset.sum_neg_distrib]
  linarith

theorem solution (m k : ℕ) (hk : k ≤ 2 * m) :
    ∑ ℓ ∈ Finset.Icc (-(m : ℤ)) m, centralCoeff m ℓ * (ℓ : ℝ) ^ k = if k = 1 then 1 else 0 := by
  rcases Nat.eq_zero_or_pos k with rfl | hkpos
  · rw [if_neg (by norm_num)]
    simp only [pow_zero, mul_one]
    exact qg_sum_odd m _ (fun ℓ => qg_cc_neg m ℓ)
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hre : ∑ ℓ ∈ Finset.Icc (-(m : ℤ)) m, centralCoeff m ℓ * (ℓ : ℝ) ^ (j+1)
      = ∑ i ∈ Finset.range (2*m+1),
          (centralCoeff m ((i:ℤ)-m) * (((i:ℤ)-m : ℤ) : ℝ)) * (((i:ℤ)-m : ℤ) : ℝ) ^ j := by
    symm
    apply Finset.sum_nbij' (fun i : ℕ => (i:ℤ) - m) (fun ℓ : ℤ => (ℓ + m).toNat)
    · intro a ha; simp only [Finset.mem_Icc, Finset.mem_range] at *; omega
    · intro a ha; simp only [Finset.mem_Icc, Finset.mem_range] at *; omega
    · intro a _; omega
    · intro a ha; simp only [Finset.mem_Icc, Finset.mem_range] at *; omega
    · intro a _; ring
  rw [hre]
  have hsum : ∀ i ∈ Finset.range (2*m+1),
      (centralCoeff m ((i:ℤ)-m) * (((i:ℤ)-m : ℤ) : ℝ)) * (((i:ℤ)-m : ℤ) : ℝ) ^ j =
      ((-1:ℝ)^(m+1) / ((2*m).choose m : ℝ)) * ((-1:ℝ)^(i) * ((2*m).choose i : ℝ) * ((i:ℝ) - m)^j)
        + (if i = m then ((0:ℝ))^j else 0) := by
    intro i hi
    have hi' : i ≤ 2*m := by simp at hi; omega
    rw [qg_key m i hi']
    push_cast
    by_cases him : i = m
    · subst him
      have hc : ((2*i).choose i : ℝ) ≠ 0 := by
        have : 0 < (2*i).choose i := Nat.choose_pos (by omega)
        positivity
      have h2 : (-1:ℝ)^(i+1)*(-1)^i = -1 := by
        rw [← pow_add, show i+1+i = 2*i+1 by ring, pow_succ, pow_mul]; norm_num
      have h5 : (-1:ℝ)^(i+i+1) = -1 := by
        rw [show i+i+1 = 2*i+1 by ring, pow_succ, pow_mul]; norm_num
      have h3 : (-1:ℝ)^(i+1)/((2*i).choose i : ℝ) * ((-1)^i * ((2*i).choose i : ℝ) * 0^j)
          = (-1)^(i+1)*(-1)^i * 0^j * (((2*i).choose i : ℝ) / ((2*i).choose i : ℝ)) := by ring
      simp only [sub_self, if_true]
      rw [h3, h2, div_self hc, h5]
      ring
    · simp only [him, if_false, add_zero]
      rw [show i + m + 1 = (m+1)+i by ring, pow_add]
      ring
  rw [Finset.sum_congr rfl hsum, Finset.sum_add_distrib, ← Finset.mul_sum, qg_fd_zero m j (by omega)]
  simp
  rw [if_pos (by omega)]
  rcases j with _ | j
  · simp
  · simp
