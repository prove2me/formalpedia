-- Prove2me | solution 1 for QGradGAW.Smooth.lemma_22
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T17:59:48.537994+00:00
-- url     : https://prove2.me/submissions/77fddbc5-7909-42b5-b197-c284b0c6d921

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

theorem qg_moments (m k : ℕ) (hk : k ≤ 2 * m) :
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

lemma l34_cosh (x : ℝ) (k : ℕ) : x ^ (2 * k) / ((2 * k).factorial : ℝ) ≤ Real.cosh x := by
  have h := Real.hasSum_cosh x
  exact le_hasSum h k (fun j _ => div_nonneg ((even_two_mul j).pow_nonneg x) (by positivity))

lemma qg_abs_key (m i : ℕ) (hi : i ≤ 2*m) :
    |centralCoeff m ((i:ℤ)-m) * (((i:ℤ)-m : ℤ) : ℝ)| ≤ ((2*m).choose i : ℝ) / ((2*m).choose m : ℝ) := by
  have hc : (0:ℝ) < ((2*m).choose m : ℝ) := by
    have : 0 < (2*m).choose m := Nat.choose_pos (by omega)
    exact_mod_cast this
  by_cases him : i = m
  · subst him
    simp [centralCoeff]
    positivity
  · rw [qg_key m i hi]
    simp only [him, if_false, add_zero]
    rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
    exact (abs_of_nonneg (by positivity)).le

lemma l34_binom_cosh (m : ℕ) (lam : ℝ) :
    ∑ i ∈ Finset.range (2*m+1), ((2*m).choose i : ℝ) * Real.cosh (lam * ((i:ℝ) - m))
      = (2 * Real.cosh (lam / 2)) ^ (2*m) := by
  have h1 : ∑ i ∈ Finset.range (2*m+1), ((2*m).choose i : ℝ) * Real.exp (lam * ((i:ℝ) - m))
      = (Real.exp (lam/2) + Real.exp (-(lam/2))) ^ (2*m) := by
    rw [add_pow]
    apply Finset.sum_congr rfl
    intro i hi
    have hi' : i ≤ 2*m := by simp at hi; omega
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
    have : ((i:ℝ) * (lam/2) + ((2*m-i : ℕ):ℝ) * (-(lam/2))) = lam * ((i:ℝ) - m) := by
      rw [Nat.cast_sub hi']; push_cast; ring
    rw [this]; ring
  have h2 : ∑ i ∈ Finset.range (2*m+1), ((2*m).choose i : ℝ) * Real.exp (-(lam * ((i:ℝ) - m)))
      = (Real.exp (lam/2) + Real.exp (-(lam/2))) ^ (2*m) := by
    rw [add_comm (Real.exp (lam/2)), add_pow]
    apply Finset.sum_congr rfl
    intro i hi
    have hi' : i ≤ 2*m := by simp at hi; omega
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
    have : ((i:ℝ) * (-(lam/2)) + ((2*m-i : ℕ):ℝ) * (lam/2)) = -(lam * ((i:ℝ) - m)) := by
      rw [Nat.cast_sub hi']; push_cast; ring
    rw [this]; ring
  have h3 : 2 * Real.cosh (lam / 2) = Real.exp (lam/2) + Real.exp (-(lam/2)) := by
    rw [Real.cosh_eq]; ring
  rw [h3]
  have : ∀ i ∈ Finset.range (2*m+1), ((2*m).choose i : ℝ) * Real.cosh (lam * ((i:ℝ) - m)) =
      (((2*m).choose i : ℝ) * Real.exp (lam * ((i:ℝ) - m)) / 2) +
      (((2*m).choose i : ℝ) * Real.exp (-(lam * ((i:ℝ) - m))) / 2) := by
    intro i _
    rw [Real.cosh_eq]; ring
  rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_div, h1, h2]
  ring

lemma l34_core (m : ℕ) (lam : ℝ) (hlam : 0 < lam) :
    ∑ i ∈ Finset.range (2*m+1), (((2*m).choose i : ℝ) / ((2*m).choose m : ℝ)) * ((i:ℝ) - m) ^ (2*m)
      ≤ ((m.factorial : ℝ)) ^ 2 * (2 * Real.cosh (lam / 2) / lam) ^ (2*m) := by
  have hc : (0:ℝ) < ((2*m).choose m : ℝ) := by
    have : 0 < (2*m).choose m := Nat.choose_pos (by omega)
    exact_mod_cast this
  have hf : (0:ℝ) < ((2*m).factorial : ℝ) := by positivity
  have hl : (0:ℝ) < lam ^ (2*m) := by positivity
  have hpt : ∀ i ∈ Finset.range (2*m+1),
      (((2*m).choose i : ℝ) / ((2*m).choose m : ℝ)) * ((i:ℝ) - m) ^ (2*m) ≤
      (((2*m).factorial : ℝ) / lam ^ (2*m) / ((2*m).choose m : ℝ)) *
        (((2*m).choose i : ℝ) * Real.cosh (lam * ((i:ℝ) - m))) := by
    intro i _
    have h := l34_cosh (lam * ((i:ℝ) - m)) m
    rw [mul_pow, div_le_iff₀ hf] at h
    have hC : (0:ℝ) ≤ ((2*m).choose i : ℝ) := by positivity
    have h' : ((i:ℝ) - m) ^ (2*m) ≤ ((2*m).factorial : ℝ) / lam ^ (2*m) * Real.cosh (lam * ((i:ℝ) - m)) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hl]
      calc ((i:ℝ) - m) ^ (2*m) * lam ^ (2*m) = lam ^ (2*m) * ((i:ℝ) - m) ^ (2*m) := mul_comm _ _
        _ ≤ _ := h
        _ = _ := mul_comm _ _
    calc (((2*m).choose i : ℝ) / ((2*m).choose m : ℝ)) * ((i:ℝ) - m) ^ (2*m)
        ≤ (((2*m).choose i : ℝ) / ((2*m).choose m : ℝ)) *
          (((2*m).factorial : ℝ) / lam ^ (2*m) * Real.cosh (lam * ((i:ℝ) - m))) :=
          mul_le_mul_of_nonneg_left h' (by positivity)
      _ = _ := by ring
  calc _ ≤ ∑ i ∈ Finset.range (2*m+1), (((2*m).factorial : ℝ) / lam ^ (2*m) / ((2*m).choose m : ℝ)) *
        (((2*m).choose i : ℝ) * Real.cosh (lam * ((i:ℝ) - m))) := Finset.sum_le_sum hpt
    _ = (((2*m).factorial : ℝ) / lam ^ (2*m) / ((2*m).choose m : ℝ)) *
        (2 * Real.cosh (lam / 2)) ^ (2*m) := by
        rw [← Finset.mul_sum, l34_binom_cosh]
    _ = ((m.factorial : ℝ)) ^ 2 * (2 * Real.cosh (lam / 2) / lam) ^ (2*m) := by
        have e := Nat.choose_mul_factorial_mul_factorial (show m ≤ 2*m by omega)
        have e2 : 2 * m - m = m := by omega
        rw [e2] at e
        have e3 : ((2*m).factorial : ℝ) = ((2*m).choose m : ℝ) * (m.factorial : ℝ) ^ 2 := by
          have : (((2*m).choose m * m.factorial * m.factorial : ℕ) : ℝ) = ((2*m).factorial : ℝ) := by
            exact_mod_cast e
          rw [← this]; push_cast; ring
        rw [e3, div_pow]
        field_simp

lemma l34_term (m k : ℕ) (hk : 2 * m ≤ k) (i : ℕ) (hi : i ∈ Finset.range (2*m+1)) :
    |centralCoeff m ((i:ℤ)-m) * (((i:ℤ)-m : ℤ) : ℝ) ^ (k+1)| ≤
      (m:ℝ) ^ (k - 2*m) * ((((2*m).choose i : ℝ) / ((2*m).choose m : ℝ)) * ((i:ℝ) - m) ^ (2*m)) := by
  have hi' : i ≤ 2*m := by simp at hi; omega
  have h1 := qg_abs_key m i hi'
  have hb : |(i:ℝ) - m| ≤ m := by
    rw [abs_le]
    have : (i:ℝ) ≤ 2 * m := by exact_mod_cast hi'
    constructor <;> linarith [(Nat.cast_nonneg i : (0:ℝ) ≤ i)]
  have hpk : |(i:ℝ) - m| ^ (k - 2*m) ≤ (m:ℝ) ^ (k - 2*m) :=
    pow_le_pow_left₀ (abs_nonneg _) hb _
  have e1 : centralCoeff m ((i:ℤ)-m) * (((i:ℤ)-m : ℤ) : ℝ) ^ (k+1) =
      (centralCoeff m ((i:ℤ)-m) * (((i:ℤ)-m : ℤ) : ℝ)) * ((i:ℝ) - m) ^ k := by
    push_cast; ring
  have e2 : |(i:ℝ) - m| ^ k = ((i:ℝ) - m) ^ (2*m) * |(i:ℝ) - m| ^ (k - 2*m) := by
    have : k = 2*m + (k - 2*m) := by omega
    conv_lhs => rw [this]
    rw [pow_add, (even_two_mul m).pow_abs]
  rw [e1, abs_mul, abs_pow, e2]
  have hC : 0 ≤ ((2*m).choose i : ℝ) / ((2*m).choose m : ℝ) := by positivity
  have hev : 0 ≤ ((i:ℝ) - m) ^ (2*m) := (even_two_mul m).pow_nonneg _
  calc |centralCoeff m ((i:ℤ)-m) * (((i:ℤ)-m : ℤ) : ℝ)| *
        (((i:ℝ) - m) ^ (2*m) * |(i:ℝ) - m| ^ (k - 2*m))
      ≤ (((2*m).choose i : ℝ) / ((2*m).choose m : ℝ)) *
        (((i:ℝ) - m) ^ (2*m) * (m:ℝ) ^ (k - 2*m)) := by
        apply mul_le_mul h1 (mul_le_mul_of_nonneg_left hpk hev) (by positivity) hC
    _ = _ := by ring


lemma l34_reindex (m k : ℕ) :
    ∑ ℓ ∈ Finset.Icc (-(m : ℤ)) m, |centralCoeff m ℓ * (ℓ : ℝ) ^ (k + 1)| =
      ∑ i ∈ Finset.range (2*m+1), |centralCoeff m ((i:ℤ)-m) * (((i:ℤ)-m : ℤ) : ℝ) ^ (k+1)| := by
  symm
  apply Finset.sum_nbij' (fun i : ℕ => (i:ℤ) - m) (fun ℓ : ℤ => (ℓ + m).toNat)
  · intro a ha; simp only [Finset.mem_Icc, Finset.mem_range] at *; omega
  · intro a ha; simp only [Finset.mem_Icc, Finset.mem_range] at *; omega
  · intro a _; omega
  · intro a ha; simp only [Finset.mem_Icc, Finset.mem_range] at *; omega
  · intro a _; rfl


lemma l22_coeff (m : ℕ) :
    ∑ ℓ ∈ Finset.Icc (-(m : ℤ)) m, |centralCoeff m ℓ * (ℓ : ℝ) ^ (2*m + 1)| ≤
      ((m.factorial : ℝ)) ^ 2 * Real.cosh 1 ^ (2*m) := by
  rw [l34_reindex]
  have hcore := l34_core m 2 (by norm_num)
  have e : (2:ℝ) / 2 = 1 := by norm_num
  rw [e] at hcore
  have e2 : 2 * Real.cosh 1 / 2 = Real.cosh 1 := by ring
  rw [e2] at hcore
  refine le_trans ?_ hcore
  apply Finset.sum_le_sum
  intro i hi
  have h := l34_term m (2*m) le_rfl i hi
  simpa using h

lemma l22_cosh_num : Real.cosh 1 ^ 2 ≤ 4 * Real.exp (-(1/2)) := by
  set s := Real.exp (1/2) with hs
  have hs0 : 0 < s := Real.exp_pos _
  have hss : s * s = Real.exp 1 := by rw [hs, ← Real.exp_add]; norm_num
  have h1 := Real.exp_one_lt_d9
  have h2 := Real.exp_one_gt_d9
  have hsU : s < 1.64873 := by
    by_contra h
    have h := not_lt.mp h
    nlinarith
  have hcosh : Real.cosh 1 ≤ (2.7182818286 + 1 / 2.7182818283) / 2 := by
    rw [Real.cosh_eq, Real.exp_neg]
    have : (Real.exp 1)⁻¹ ≤ 1 / 2.7182818283 := by
      rw [one_div]; exact inv_anti₀ (by norm_num) h2.le
    linarith
  have hc0 : 0 ≤ Real.cosh 1 := (Real.cosh_pos 1).le
  have hsq : Real.cosh 1 ^ 2 ≤ ((2.7182818286 + 1 / 2.7182818283) / 2) ^ 2 :=
    pow_le_pow_left₀ hc0 hcosh 2
  have hneg : Real.exp (-(1/2)) = s⁻¹ := by rw [hs, Real.exp_neg]
  rw [hneg]
  have key : ((2.7182818286 + 1 / 2.7182818283) / 2 : ℝ) ^ 2 * 1.64873 ≤ 4 := by norm_num
  have : Real.cosh 1 ^ 2 * s ≤ 4 := by
    calc Real.cosh 1 ^ 2 * s ≤ ((2.7182818286 + 1 / 2.7182818283) / 2) ^ 2 * 1.64873 :=
          mul_le_mul hsq hsU.le hs0.le (by positivity)
      _ ≤ 4 := key
  rw [← div_eq_mul_inv, le_div_iff₀ hs0]
  linarith

lemma l22_num (m : ℕ) :
    ((m.factorial : ℝ)) ^ 2 * Real.cosh 1 ^ (2*m) ≤
      Real.exp (-((m : ℝ) / 2)) * ((2*m+1).factorial : ℝ) := by
  have h1 : Real.cosh 1 ^ (2*m) ≤ 4 ^ m * Real.exp (-((m : ℝ) / 2)) := by
    calc Real.cosh 1 ^ (2*m) = (Real.cosh 1 ^ 2) ^ m := by rw [← pow_mul]
      _ ≤ (4 * Real.exp (-(1/2))) ^ m := pow_le_pow_left₀ (by positivity) l22_cosh_num m
      _ = 4 ^ m * Real.exp (-((m : ℝ) / 2)) := by
          rw [mul_pow, ← Real.exp_nat_mul]; congr 2; ring
  have h2 : (4:ℝ) ^ m ≤ ((2*m+1 : ℕ) : ℝ) * ((2*m).choose m : ℝ) := by
    have := Nat.four_pow_le_two_mul_add_one_mul_central_binom m
    exact_mod_cast this
  have e : ((2*m).factorial : ℝ) = ((2*m).choose m : ℝ) * (m.factorial : ℝ) ^ 2 := by
    have e0 := Nat.choose_mul_factorial_mul_factorial (show m ≤ 2*m by omega)
    have e2 : 2 * m - m = m := by omega
    rw [e2] at e0
    have : (((2*m).choose m * m.factorial * m.factorial : ℕ) : ℝ) = ((2*m).factorial : ℝ) := by
      exact_mod_cast e0
    rw [← this]; push_cast; ring
  have e3 : ((2*m+1).factorial : ℝ) = ((2*m+1 : ℕ) : ℝ) * ((2*m).factorial : ℝ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have hE := Real.exp_pos (-((m : ℝ) / 2))
  have hm2 : (0:ℝ) ≤ (m.factorial : ℝ) ^ 2 := by positivity
  calc ((m.factorial : ℝ)) ^ 2 * Real.cosh 1 ^ (2*m)
      ≤ ((m.factorial : ℝ)) ^ 2 * (4 ^ m * Real.exp (-((m : ℝ) / 2))) :=
        mul_le_mul_of_nonneg_left h1 hm2
    _ = Real.exp (-((m : ℝ) / 2)) * ((4:ℝ) ^ m * (m.factorial : ℝ) ^ 2) := by ring
    _ ≤ Real.exp (-((m : ℝ) / 2)) * ((((2*m+1 : ℕ) : ℝ) * ((2*m).choose m : ℝ)) * (m.factorial : ℝ) ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ hE.le
        exact mul_le_mul_of_nonneg_right h2 hm2
    _ = Real.exp (-((m : ℝ) / 2)) * ((2*m+1).factorial : ℝ) := by
        rw [e3, e]; ring

lemma l22_agree {f : ℝ → ℝ} {I s : Set ℝ} {n : ℕ} (hsI : s ⊆ I) (hs : UniqueDiffOn ℝ s)
    (hI : UniqueDiffOn ℝ I) (hcd : ContDiffOn ℝ n f I) {y : ℝ} (hy : y ∈ s) :
    iteratedDerivWithin n f s y = iteratedDerivWithin n f I y := by
  rw [iteratedDerivWithin_eq_iteratedFDerivWithin, iteratedDerivWithin_eq_iteratedFDerivWithin,
    iteratedFDerivWithin_subset hsI hs hI hcd hy]

lemma l22_taylor (m : ℕ) (δ : ℝ) (f : ℝ → ℝ)
    (hcd : ContDiffOn ℝ (2*m : ℕ) f (Set.Icc (-((m:ℝ)*δ)) ((m:ℝ)*δ)))
    (hd : DifferentiableOn ℝ (iteratedDerivWithin (2*m) f (Set.Icc (-((m:ℝ)*δ)) ((m:ℝ)*δ)))
      (Set.Icc (-((m:ℝ)*δ)) ((m:ℝ)*δ)))
    (B : ℝ) (hB : ∀ ξ ∈ Set.Icc (-((m:ℝ)*δ)) ((m:ℝ)*δ),
      |iteratedDerivWithin (2 * m + 1) f (Set.Icc (-((m:ℝ)*δ)) ((m:ℝ)*δ)) ξ| ≤ B)
    (x : ℝ) (hx0 : x ≠ 0) (hx : |x| ≤ (m:ℝ) * δ) :
    |f x - ∑ k ∈ Finset.range (2*m+1),
        iteratedDerivWithin k f (Set.Icc (-((m:ℝ)*δ)) ((m:ℝ)*δ)) 0 * x ^ k / (k.factorial : ℝ)| ≤
      B * |x| ^ (2*m+1) / ((2*m+1).factorial : ℝ) := by
  set I : Set ℝ := Set.Icc (-((m:ℝ)*δ)) ((m:ℝ)*δ) with hI
  have hpos : 0 < (m:ℝ) * δ := lt_of_lt_of_le (abs_pos.2 hx0) hx
  have hUI : UniqueDiffOn ℝ I := uniqueDiffOn_Icc (by linarith)
  have hxI : x ∈ I := abs_le.mp hx
  have h0I : (0:ℝ) ∈ I := ⟨by linarith, by linarith⟩
  have hJI : Set.uIcc 0 x ⊆ I := Set.uIcc_subset_Icc h0I hxI
  have hUJ : UniqueDiffOn ℝ (Set.uIcc 0 x) := uniqueDiffOn_uIcc (Ne.symm hx0)
  have hdJ : DifferentiableOn ℝ (iteratedDerivWithin (2*m) f (Set.uIcc 0 x)) (Set.uIoo 0 x) := by
    have h1 : DifferentiableOn ℝ (iteratedDerivWithin (2*m) f I) (Set.uIoo 0 x) :=
      hd.mono ((Set.uIoo_subset_uIcc_self).trans hJI)
    refine h1.congr (fun y hy => ?_)
    exact l22_agree hJI hUJ hUI hcd (Set.uIoo_subset_uIcc_self hy)
  obtain ⟨x', hx', h⟩ := taylor_mean_remainder_lagrange (f := f) (x := x) (x₀ := 0) (n := 2*m)
    (Ne.symm hx0) (hcd.mono hJI) hdJ
  rw [taylor_within_apply] at h
  have hsum : ∑ k ∈ Finset.range (2*m+1),
      ((k.factorial : ℝ)⁻¹ * (x - 0) ^ k) • iteratedDerivWithin k f (Set.uIcc 0 x) 0 =
      ∑ k ∈ Finset.range (2*m+1),
        iteratedDerivWithin k f I 0 * x ^ k / (k.factorial : ℝ) := by
    apply Finset.sum_congr rfl
    intro k hk
    have hk' : k ≤ 2*m := by simp at hk; omega
    have hcdk : ContDiffOn ℝ k f I := hcd.of_le (by exact_mod_cast hk')
    rw [l22_agree hJI hUJ hUI hcdk (Set.left_mem_uIcc)]
    simp only [smul_eq_mul, sub_zero]
    ring
  rw [hsum] at h
  -- identify the (2m+1)-th derivative
  have hx'J : x' ∈ Set.uIcc 0 x := Set.uIoo_subset_uIcc_self hx'
  have hJnhds : Set.uIcc 0 x ∈ nhds x' := by
    apply Icc_mem_nhds_iff.2
    simpa [Set.uIoo, Set.uIcc] using hx'
  have hI_nhds : I ∈ nhds x' := Filter.mem_of_superset hJnhds hJI
  have hderiv : iteratedDerivWithin (2 * m + 1) f (Set.uIcc 0 x) x' =
      iteratedDerivWithin (2 * m + 1) f I x' := by
    rw [iteratedDerivWithin_succ, iteratedDerivWithin_succ, derivWithin_of_mem_nhds hJnhds,
      derivWithin_of_mem_nhds hI_nhds]
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [hJnhds] with y hy using l22_agree hJI hUJ hUI hcd hy
  rw [h, hderiv]
  have hF : (0:ℝ) < ((2*m+1).factorial : ℝ) := by positivity
  calc |iteratedDerivWithin (2 * m + 1) f I x' * (x - 0) ^ (2 * m + 1) / ((2 * m + 1).factorial : ℝ)|
      = |iteratedDerivWithin (2 * m + 1) f I x'| * |x| ^ (2 * m + 1) / ((2 * m + 1).factorial : ℝ) := by
        rw [abs_div, abs_mul, abs_pow, sub_zero, abs_of_pos hF]
    _ ≤ B * |x| ^ (2*m+1) / ((2*m+1).factorial : ℝ) := by
        gcongr
        exact hB x' (hJI hx'J)

theorem solution (m : ℕ) (hm : 1 ≤ m) (δ : ℝ) (hδ : 0 < δ) (f : ℝ → ℝ)
    (hf : ∀ j < 2 * m + 1, DifferentiableOn ℝ
      (iteratedDerivWithin j f (Set.Icc (-((m : ℝ) * δ)) ((m : ℝ) * δ)))
      (Set.Icc (-((m : ℝ) * δ)) ((m : ℝ) * δ)))
    (B : ℝ)
    (hB : ∀ ξ ∈ Set.Icc (-((m : ℝ) * δ)) ((m : ℝ) * δ),
      |iteratedDerivWithin (2 * m + 1) f (Set.Icc (-((m : ℝ) * δ)) ((m : ℝ) * δ)) ξ| ≤ B) :
    |deriv f 0 * δ - ∑ ℓ ∈ Finset.Icc (-(m : ℤ)) m, centralCoeff m ℓ * f ((ℓ : ℝ) * δ)| ≤
      Real.exp (-((m : ℝ) / 2)) * B * |δ| ^ (2 * m + 1) := by
  set I : Set ℝ := Set.Icc (-((m:ℝ)*δ)) ((m:ℝ)*δ) with hI
  have hmr : (1:ℝ) ≤ m := by exact_mod_cast hm
  have hpos : 0 < (m:ℝ) * δ := by positivity
  have hUI : UniqueDiffOn ℝ I := uniqueDiffOn_Icc (by linarith)
  have h0I : (0:ℝ) ∈ I := ⟨by linarith, by linarith⟩
  have hcd : ContDiffOn ℝ (2*m : ℕ) f I := by
    have := contDiffOn_of_differentiableOn_deriv (𝕜 := ℝ) (f := f) (s := I) (n := ((2*m : ℕ) : ℕ∞))
      (fun j hj => hf j (by
        have : j ≤ 2*m := by exact_mod_cast hj
        omega))
    exact_mod_cast this
  have hd := hf (2*m) (by omega)
  have hBnn : 0 ≤ B := (abs_nonneg _).trans (hB 0 h0I)
  set c : ℕ → ℝ := fun k => iteratedDerivWithin k f I 0 with hc
  set P : ℝ → ℝ := fun x => ∑ k ∈ Finset.range (2*m+1), c k * x ^ k / (k.factorial : ℝ) with hP
  have hrem : ∀ ℓ ∈ Finset.Icc (-(m : ℤ)) m, |centralCoeff m ℓ * (f ((ℓ:ℝ) * δ) - P ((ℓ:ℝ) * δ))| ≤
      B * δ ^ (2*m+1) / ((2*m+1).factorial : ℝ) * |centralCoeff m ℓ * (ℓ : ℝ) ^ (2*m+1)| := by
    intro ℓ hℓ
    by_cases h0 : ℓ = 0
    · subst h0; simp [centralCoeff]
    · have hℓm : |(ℓ:ℝ)| ≤ m := by
        simp only [Finset.mem_Icc] at hℓ
        rw [abs_le]; constructor <;> [skip; skip] <;> (norm_cast; omega)
      have hx : |(ℓ:ℝ) * δ| ≤ (m:ℝ) * δ := by
        rw [abs_mul, abs_of_pos hδ]
        exact mul_le_mul_of_nonneg_right hℓm hδ.le
      have hx0 : (ℓ:ℝ) * δ ≠ 0 := mul_ne_zero (by exact_mod_cast h0) hδ.ne'
      have ht := l22_taylor m δ f hcd hd B hB ((ℓ:ℝ) * δ) hx0 hx
      rw [abs_mul]
      have hF : (0:ℝ) < ((2*m+1).factorial : ℝ) := by positivity
      have : |centralCoeff m ℓ * (ℓ : ℝ) ^ (2*m+1)| = |centralCoeff m ℓ| * |(ℓ:ℝ)| ^ (2*m+1) := by
        rw [abs_mul, abs_pow]
      rw [this]
      calc |centralCoeff m ℓ| * |f ((ℓ:ℝ) * δ) - P ((ℓ:ℝ) * δ)|
          ≤ |centralCoeff m ℓ| * (B * |(ℓ:ℝ) * δ| ^ (2*m+1) / ((2*m+1).factorial : ℝ)) :=
            mul_le_mul_of_nonneg_left ht (abs_nonneg _)
        _ = _ := by
            rw [abs_mul, abs_of_pos hδ, mul_pow]; ring
  have hc1 : c 1 = deriv f 0 := by
    simp only [hc]
    rw [iteratedDerivWithin_one]
    exact derivWithin_of_mem_nhds (Icc_mem_nhds (by linarith) (by linarith))
  have hP1 : ∑ ℓ ∈ Finset.Icc (-(m : ℤ)) m, centralCoeff m ℓ * P ((ℓ:ℝ) * δ) = c 1 * δ := by
    have e1 : ∀ ℓ : ℤ, centralCoeff m ℓ * P ((ℓ:ℝ) * δ) =
        ∑ k ∈ Finset.range (2*m+1), (c k * δ ^ k / (k.factorial : ℝ)) *
          (centralCoeff m ℓ * (ℓ:ℝ) ^ k) := by
      intro ℓ
      simp only [hP]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    rw [Finset.sum_congr rfl (fun ℓ _ => e1 ℓ), Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    rw [Finset.sum_congr rfl (fun k hk => by
      rw [qg_moments m k (by simp at hk; omega)])]
    have : (1:ℕ) ∈ Finset.range (2*m+1) := by simp; omega
    simp [Finset.sum_ite_eq, this]
  have hsplit : deriv f 0 * δ - ∑ ℓ ∈ Finset.Icc (-(m : ℤ)) m, centralCoeff m ℓ * f ((ℓ : ℝ) * δ)
      = - ∑ ℓ ∈ Finset.Icc (-(m : ℤ)) m, centralCoeff m ℓ * (f ((ℓ:ℝ) * δ) - P ((ℓ:ℝ) * δ)) := by
    have : ∑ ℓ ∈ Finset.Icc (-(m : ℤ)) m, centralCoeff m ℓ * f ((ℓ : ℝ) * δ) =
        ∑ ℓ ∈ Finset.Icc (-(m : ℤ)) m, centralCoeff m ℓ * P ((ℓ:ℝ) * δ) +
        ∑ ℓ ∈ Finset.Icc (-(m : ℤ)) m, centralCoeff m ℓ * (f ((ℓ:ℝ) * δ) - P ((ℓ:ℝ) * δ)) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro ℓ _
      ring
    rw [this, hP1, hc1]
    ring
  rw [hsplit, abs_neg]
  have hF : (0:ℝ) < ((2*m+1).factorial : ℝ) := by positivity
  have hK : 0 ≤ B * δ ^ (2*m+1) / ((2*m+1).factorial : ℝ) := by positivity
  calc |∑ ℓ ∈ Finset.Icc (-(m : ℤ)) m, centralCoeff m ℓ * (f ((ℓ:ℝ) * δ) - P ((ℓ:ℝ) * δ))|
      ≤ ∑ ℓ ∈ Finset.Icc (-(m : ℤ)) m, |centralCoeff m ℓ * (f ((ℓ:ℝ) * δ) - P ((ℓ:ℝ) * δ))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ ℓ ∈ Finset.Icc (-(m : ℤ)) m, B * δ ^ (2*m+1) / ((2*m+1).factorial : ℝ) *
          |centralCoeff m ℓ * (ℓ : ℝ) ^ (2*m+1)| := Finset.sum_le_sum hrem
    _ = B * δ ^ (2*m+1) / ((2*m+1).factorial : ℝ) *
          ∑ ℓ ∈ Finset.Icc (-(m : ℤ)) m, |centralCoeff m ℓ * (ℓ : ℝ) ^ (2*m+1)| := by
        rw [Finset.mul_sum]
    _ ≤ B * δ ^ (2*m+1) / ((2*m+1).factorial : ℝ) *
          (Real.exp (-((m : ℝ) / 2)) * ((2*m+1).factorial : ℝ)) :=
        mul_le_mul_of_nonneg_left ((l22_coeff m).trans (l22_num m)) hK
    _ = Real.exp (-((m : ℝ) / 2)) * B * |δ| ^ (2 * m + 1) := by
        rw [abs_of_pos hδ]
        field_simp
