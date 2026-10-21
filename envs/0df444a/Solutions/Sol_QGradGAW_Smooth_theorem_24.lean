-- Prove2me | solution 1 for QGradGAW.Smooth.theorem_24
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T18:14:07.673794+00:00
-- url     : https://prove2.me/submissions/1174ad66-067f-4d8f-baf1-b6de74d3fc52

import Mathlib
import Definitions.Def_QGradGAW_Smooth_Setting

set_option autoImplicit false
open MeasureTheory ProbabilityTheory QAlgorithms QGradGAW.Smooth
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

lemma l34_num : Real.exp (7/6) + Real.exp (-(7/6)) ≤ 7/3 * Real.exp (5/12) := by
  set u := Real.exp (1/12) with hu
  have hu0 : 0 < u := Real.exp_pos _
  have h12 : u ^ 12 = Real.exp 1 := by rw [hu, ← Real.exp_nat_mul]; norm_num
  have hU : u < 108691/100000 := by
    by_contra h
    have h := not_lt.mp h
    have h1 := pow_le_pow_left₀ (by norm_num) h 12
    have h2 := Real.exp_one_lt_d9
    rw [h12] at h1
    norm_num at h1 h2
    linarith
  have hL : 10869/10000 < u := by
    by_contra h
    have h := not_lt.mp h
    have h1 := pow_le_pow_left₀ hu0.le h 12
    have h2 := Real.exp_one_gt_d9
    rw [h12] at h1
    norm_num at h1 h2
    linarith
  have e1 : Real.exp (7/6) = u^14 := by rw [hu, ← Real.exp_nat_mul]; norm_num
  have e2 : Real.exp (-(7/6)) = (u^14)⁻¹ := by rw [← e1, Real.exp_neg]
  have e3 : Real.exp (5/12) = u^5 := by rw [hu, ← Real.exp_nat_mul]; norm_num
  rw [e1, e2, e3]
  have hp : 0 < u^14 := by positivity
  have key : u^28 + 1 ≤ 7/3 * u^19 := by
    have a1 : u^28 ≤ (108691/100000)^28 := pow_le_pow_left₀ hu0.le hU.le 28
    have a2 : (10869/10000)^19 ≤ u^19 := pow_le_pow_left₀ (by norm_num) hL.le 19
    have a3 : ((108691/100000 : ℝ))^28 + 1 ≤ 7/3 * (10869/10000)^19 := by norm_num
    linarith
  have : (u^14 + (u^14)⁻¹) = (u^28+1)/u^14 := by field_simp
  rw [this, div_le_iff₀ hp]
  calc u^28 + 1 ≤ 7/3 * u^19 := key
    _ = 7/3 * u^5 * u^14 := by ring

lemma l34_stirling_up (m : ℕ) (hm : 1 ≤ m) :
    (m.factorial : ℝ) ≤ Real.exp 1 * Real.sqrt m * ((m:ℝ) / Real.exp 1) ^ m := by
  have h1 : Stirling.stirlingSeq m ≤ Stirling.stirlingSeq 1 := by
    have := Stirling.stirlingSeq'_antitone (show 0 ≤ m - 1 by omega)
    simpa [Nat.sub_add_cancel hm] using this
  rw [Stirling.stirlingSeq_one] at h1
  unfold Stirling.stirlingSeq at h1
  have hmr : (0:ℝ) < m := by exact_mod_cast hm
  have hpos : 0 < Real.sqrt (2 * (m:ℝ)) * ((m:ℝ) / Real.exp 1) ^ m := by positivity
  rw [div_le_iff₀ hpos] at h1
  have e : Real.sqrt (2 * (m:ℝ)) = Real.sqrt 2 * Real.sqrt m := Real.sqrt_mul (by norm_num) _
  have h2 : (0:ℝ) < Real.sqrt 2 := by positivity
  calc (m.factorial : ℝ) ≤ Real.exp 1 / Real.sqrt 2 * (Real.sqrt (2 * (m:ℝ)) * ((m:ℝ) / Real.exp 1) ^ m) := h1
    _ = Real.exp 1 * Real.sqrt m * ((m:ℝ) / Real.exp 1) ^ m := by
        rw [e]; field_simp


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

lemma l34_range_bound (m k : ℕ) (hk : 2 * m ≤ k) :
    ∑ i ∈ Finset.range (2*m+1), |centralCoeff m ((i:ℤ)-m) * (((i:ℤ)-m : ℤ) : ℝ) ^ (k+1)| ≤
      (m:ℝ) ^ (k - 2*m) * (((m.factorial : ℝ)) ^ 2 *
        (2 * Real.cosh (7/6) / (7/3)) ^ (2*m)) := by
  have hcore := l34_core m (7/3) (by norm_num)
  have e : (7/3:ℝ) / 2 = 7/6 := by norm_num
  rw [e] at hcore
  calc _ ≤ ∑ i ∈ Finset.range (2*m+1), (m:ℝ) ^ (k - 2*m) *
        ((((2*m).choose i : ℝ) / ((2*m).choose m : ℝ)) * ((i:ℝ) - m) ^ (2*m)) :=
        Finset.sum_le_sum (fun i hi => l34_term m k hk i hi)
    _ = (m:ℝ) ^ (k - 2*m) * ∑ i ∈ Finset.range (2*m+1),
        ((((2*m).choose i : ℝ) / ((2*m).choose m : ℝ)) * ((i:ℝ) - m) ^ (2*m)) := by
        rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left hcore (by positivity)

lemma l34_final (m k : ℕ) (hm : 2 ≤ m) (hk : 2 * m ≤ k) :
    (m:ℝ) ^ (k - 2*m) * (((m.factorial : ℝ)) ^ 2 * (2 * Real.cosh (7/6) / (7/3)) ^ (2*m)) ≤
      6 * Real.exp (-(7 * (m : ℝ) / 6)) * (m : ℝ) ^ ((k : ℝ) + 3 / 2) := by
  have hMge : (2:ℝ) ≤ m := by exact_mod_cast hm
  have hMpos : (0:ℝ) < m := by linarith
  set M : ℝ := (m:ℝ) with hM
  have hQ : 2 * Real.cosh (7/6) / (7/3) ≤ Real.exp (5/12) := by
    have h2 : 2 * Real.cosh (7/6) = Real.exp (7/6) + Real.exp (-(7/6)) := by
      rw [Real.cosh_eq]; ring
    rw [h2, div_le_iff₀ (by norm_num)]
    have := l34_num
    linarith
  have hQ0 : 0 ≤ 2 * Real.cosh (7/6) / (7/3) := by positivity
  have hQp : (2 * Real.cosh (7/6) / (7/3)) ^ (2*m) ≤ Real.exp (5 * M / 6) := by
    calc (2 * Real.cosh (7/6) / (7/3)) ^ (2*m) ≤ (Real.exp (5/12)) ^ (2*m) :=
          pow_le_pow_left₀ hQ0 hQ _
      _ = Real.exp (5 * M / 6) := by
          rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hst := l34_stirling_up m (by omega)
  have hst2 : ((m.factorial : ℝ)) ^ 2 ≤ Real.exp 1 ^ 2 * M * (M ^ (2*m) / Real.exp (2 * M)) := by
    have h0 : (0:ℝ) ≤ (m.factorial : ℝ) := by positivity
    have := pow_le_pow_left₀ h0 hst 2
    refine this.trans (le_of_eq ?_)
    have e3 : Real.exp 1 ^ (2*m) = Real.exp (2*M) := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    have h5 : ((m:ℝ)^2 / Real.exp 1 ^ 2)^m = (m:ℝ)^(2*m)/Real.exp (2*M) := by
      rw [div_pow, ← pow_mul, ← pow_mul, e3]
    rw [mul_pow, mul_pow, Real.sq_sqrt hMpos.le, ← pow_mul, mul_comm m 2, pow_mul, div_pow,
      h5]
  have hexp1 : Real.exp 1 ^ 2 ≤ 7.39 := by
    have := Real.exp_one_lt_d9
    have h0 := Real.exp_pos 1
    nlinarith
  have hsq : (1.25:ℝ) ≤ Real.sqrt M := by
    apply Real.le_sqrt_of_sq_le
    nlinarith
  have hrpow : M ^ ((k:ℝ) + 3/2) = M ^ k * (M * Real.sqrt M) := by
    have : ((k:ℝ) + 3/2) = (k:ℝ) + (1 + 1/2) := by norm_num
    rw [this, Real.rpow_add hMpos, Real.rpow_add hMpos, Real.rpow_natCast, Real.rpow_one,
      ← Real.sqrt_eq_rpow]
  have hkk : M ^ (k - 2*m) * M ^ (2*m) = M ^ k := by
    rw [← pow_add, Nat.sub_add_cancel hk]
  have hEE : Real.exp (5 * M / 6) / Real.exp (2 * M) = Real.exp (-(7 * M / 6)) := by
    rw [← Real.exp_sub]; congr 1; ring
  have hE0 : 0 < Real.exp (-(7 * M / 6)) := Real.exp_pos _
  have hMk : 0 < M ^ k := by positivity
  have hQpow0 : 0 ≤ (2 * Real.cosh (7/6) / (7/3)) ^ (2*m) := by positivity
  have hrhs0 : 0 ≤ Real.exp 1 ^ 2 * M * (M ^ (2*m) / Real.exp (2 * M)) := by positivity
  calc M ^ (k - 2*m) * (((m.factorial : ℝ)) ^ 2 * (2 * Real.cosh (7/6) / (7/3)) ^ (2*m))
      ≤ M ^ (k - 2*m) * ((Real.exp 1 ^ 2 * M * (M ^ (2*m) / Real.exp (2 * M))) *
          Real.exp (5 * M / 6)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul hst2 hQp hQpow0 hrhs0
    _ = Real.exp 1 ^ 2 * M * (M ^ (k - 2*m) * M ^ (2*m)) *
          (Real.exp (5 * M / 6) / Real.exp (2 * M)) := by ring
    _ = Real.exp 1 ^ 2 * (M * M ^ k * Real.exp (-(7 * M / 6))) := by rw [hkk, hEE]; ring
    _ ≤ 6 * Real.sqrt M * (M * M ^ k * Real.exp (-(7 * M / 6))) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        linarith
    _ = 6 * Real.exp (-(7 * M / 6)) * M ^ ((k : ℝ) + 3 / 2) := by
        rw [hrpow]; ring

lemma l34_m1 (k : ℕ) (hk : 2 * 1 ≤ k) :
    ∑ i ∈ Finset.range (2*1+1), |centralCoeff 1 ((i:ℤ)-(1:ℕ)) * (((i:ℤ)-(1:ℕ) : ℤ) : ℝ) ^ (k+1)|
      ≤ 6 * Real.exp (-(7 * ((1:ℕ) : ℝ) / 6)) * ((1:ℕ) : ℝ) ^ ((k : ℝ) + 3 / 2) := by
  have h := Finset.sum_le_sum (fun i hi => l34_term 1 k hk i hi)
  refine h.trans ?_
  norm_num [Finset.sum_range_succ, Nat.choose]
  have hE : (6:ℝ)⁻¹ ≤ Real.exp (-(7/6)) := by
    rw [Real.exp_neg, inv_le_inv₀ (by norm_num) (Real.exp_pos _)]
    by_contra hc
    have hc := not_le.mp hc
    have h6 : Real.exp (7/6) ^ 6 = Real.exp 1 ^ 7 := by
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]; norm_num
    have h7 : (6:ℝ) ^ 6 < Real.exp (7/6) ^ 6 := pow_lt_pow_left₀ hc (by norm_num) (by norm_num)
    rw [h6] at h7
    have h8 := Real.exp_one_lt_d9
    have h9 : Real.exp 1 ^ 7 < (2.7182818286:ℝ) ^ 7 :=
      pow_lt_pow_left₀ h8 (Real.exp_pos 1).le (by norm_num)
    norm_num at h7 h9
    linarith
  linarith

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

theorem l34_main (m k : ℕ) (hm : 1 ≤ m) (hk : 2 * m ≤ k) :
    ∑ ℓ ∈ Finset.Icc (-(m : ℤ)) m, |centralCoeff m ℓ * (ℓ : ℝ) ^ (k + 1)| ≤
      6 * Real.exp (-(7 * (m : ℝ) / 6)) * (m : ℝ) ^ ((k : ℝ) + 3 / 2) := by
  rw [l34_reindex]
  rcases (show m = 1 ∨ 2 ≤ m by omega) with rfl | h2
  · exact l34_m1 k hk
  · exact (l34_range_bound m k hk).trans (l34_final m k h2 hk)

section L36
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]

lemma l36_int {d : ℕ} (X : Fin d → Ω → ℝ) (hXm : ∀ i, Measurable (X i))
    (hbdd : ∀ i ω, X i ω ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2))
    {ι : Type*} [Fintype ι] (w : ι → Fin d) :
    Integrable (fun ω => ∏ j, X (w j) ω) P := by
  refine Integrable.of_bound (C := 1) ?_ ?_
  · exact (Finset.measurable_prod _ (fun j _ => hXm (w j))).aestronglyMeasurable
  · refine Filter.Eventually.of_forall (fun ω => ?_)
    rw [norm_prod]
    apply Finset.prod_le_one (fun _ _ => norm_nonneg _)
    intro j _
    have := hbdd (w j) ω
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [this.1, this.2]

lemma l36_nonneg {d : ℕ} (X : Fin d → Ω → ℝ) (hXm : ∀ i, Measurable (X i)) (hind : iIndepFun X P)
    (hmom : ∀ i, ∀ j : ℕ, ∫ ω, X i ω ^ (2 * j + 1) ∂P = 0)
    {ι : Type*} [Fintype ι] (w : ι → Fin d) :
    0 ≤ ∫ ω, ∏ j, X (w j) ω ∂P := by
  classical
  have h1 : ∀ ω, ∏ j, X (w j) ω =
      ∏ i, (X i ω) ^ (Finset.univ.filter (fun j => w j = i)).card := by
    intro ω
    rw [← Finset.prod_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ) (g := w)
      (fun x _ => Finset.mem_univ _)]
    apply Finset.prod_congr rfl
    intro i _
    rw [← Finset.prod_const]
    apply Finset.prod_congr rfl
    intro j hj
    rw [(Finset.mem_filter.1 hj).2]
  simp_rw [h1]
  rw [iIndepFun.integral_fun_prod_comp (f := fun i x => x ^ (Finset.univ.filter (fun j => w j = i)).card)
    hind (fun i => (hXm i).aemeasurable) (fun i => (continuous_pow _).aestronglyMeasurable)]
  apply Finset.prod_nonneg
  intro i _
  rcases Nat.even_or_odd (Finset.univ.filter (fun j => w j = i)).card with he | ⟨j, hj⟩
  · exact integral_nonneg (fun ω => he.pow_nonneg _)
  · rw [hj]; exact (hmom i j).ge

lemma l36_expand {d k : ℕ} (X : Fin d → Ω → ℝ) (hXm : ∀ i, Measurable (X i))
    (hbdd : ∀ i ω, X i ω ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2))
    (G : (Fin k → Fin d) → ℝ) :
    ∫ ω, (∑ α : Fin k → Fin d, G α * ∏ j, X (α j) ω) ^ 2 ∂P =
      ∑ α : Fin k → Fin d, ∑ β : Fin k → Fin d,
        G α * G β * ∫ ω, ∏ j : Fin k ⊕ Fin k, X (Sum.elim α β j) ω ∂P := by
  have e : ∀ ω, (∑ α : Fin k → Fin d, G α * ∏ j, X (α j) ω) ^ 2 =
      ∑ α : Fin k → Fin d, ∑ β : Fin k → Fin d,
        G α * G β * ∏ j : Fin k ⊕ Fin k, X (Sum.elim α β j) ω := by
    intro ω
    rw [sq, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl; intro α _
    apply Finset.sum_congr rfl; intro β _
    rw [Fintype.prod_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr]
    ring
  simp_rw [e]
  rw [integral_finsetSum _ (fun α _ => integrable_finsetSum _ (fun β _ =>
    (l36_int P X hXm hbdd (Sum.elim α β)).const_mul _))]
  apply Finset.sum_congr rfl; intro α _
  rw [integral_finsetSum _ (fun β _ => (l36_int P X hXm hbdd (Sum.elim α β)).const_mul _)]
  apply Finset.sum_congr rfl; intro β _
  rw [integral_const_mul]

lemma l36_second {d k : ℕ} (X : Fin d → Ω → ℝ) (hXm : ∀ i, Measurable (X i))
    (hbdd : ∀ i ω, X i ω ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2))
    (hind : iIndepFun X P)
    (hmom : ∀ i, ∀ j : ℕ, ∫ ω, X i ω ^ (2 * j + 1) ∂P = 0)
    (H : (Fin k → Fin d) → ℝ) (hH : ∀ α, |H α| ≤ 1) :
    ∫ ω, (∑ α : Fin k → Fin d, H α * ∏ j, X (α j) ω) ^ 2 ∂P ≤
      ∫ ω, (∑ i, X i ω) ^ (2 * k) ∂P := by
  have hpow : ∀ ω, (∑ i, X i ω) ^ k = ∑ α : Fin k → Fin d, ∏ j, X (α j) ω := by
    intro ω
    have := Finset.prod_univ_sum (fun (_ : Fin k) => (Finset.univ : Finset (Fin d)))
      (fun _ i => X i ω)
    simpa [Fintype.piFinset_univ] using this
  have hZ : ∀ ω, (∑ i, X i ω) ^ (2 * k) =
      (∑ α : Fin k → Fin d, (fun _ => (1:ℝ)) α * ∏ j, X (α j) ω) ^ 2 := by
    intro ω
    rw [pow_mul', hpow]
    simp
  simp_rw [hZ]
  rw [l36_expand P X hXm hbdd, l36_expand P X hXm hbdd]
  apply Finset.sum_le_sum; intro α _
  apply Finset.sum_le_sum; intro β _
  have hM := l36_nonneg P X hXm hind hmom (Sum.elim α β)
  have h1 : H α * H β ≤ 1 := by
    calc H α * H β ≤ |H α * H β| := le_abs_self _
      _ = |H α| * |H β| := abs_mul _ _
      _ ≤ 1 * 1 := mul_le_mul (hH α) (hH β) (abs_nonneg _) (by norm_num)
      _ = 1 := by norm_num
  calc H α * H β * ∫ ω, ∏ j : Fin k ⊕ Fin k, X (Sum.elim α β j) ω ∂P
      ≤ 1 * ∫ ω, ∏ j : Fin k ⊕ Fin k, X (Sum.elim α β j) ω ∂P :=
        mul_le_mul_of_nonneg_right h1 hM
    _ = _ := by ring

lemma l36_cosh (x : ℝ) (k : ℕ) : x ^ (2 * k) / ((2 * k).factorial : ℝ) ≤ Real.cosh x := by
  have h := Real.hasSum_cosh x
  exact le_hasSum h k (fun j _ => div_nonneg ((even_two_mul j).pow_nonneg x) (by positivity))

lemma l36_subG {d : ℕ} (X : Fin d → Ω → ℝ) (hXm : ∀ i, Measurable (X i))
    (hbdd : ∀ i ω, X i ω ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2))
    (hind : iIndepFun X P)
    (hmom : ∀ i, ∀ j : ℕ, ∫ ω, X i ω ^ (2 * j + 1) ∂P = 0) :
    HasSubgaussianMGF (fun ω => ∑ i ∈ Finset.univ, X i ω)
      (∑ i : Fin d, (‖(1/2:ℝ) - -(1/2)‖₊/2)^2) P := by
  apply HasSubgaussianMGF.sum_of_iIndepFun hind (c := fun _ => (‖(1/2:ℝ) - -(1/2)‖₊/2)^2)
  intro i _
  apply hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero (hXm i).aemeasurable
  · exact Filter.Eventually.of_forall (hbdd i)
  · simpa using hmom i 0

lemma l36_moment {d k : ℕ} (X : Fin d → Ω → ℝ) (hXm : ∀ i, Measurable (X i))
    (hbdd : ∀ i ω, X i ω ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2))
    (hind : iIndepFun X P)
    (hmom : ∀ i, ∀ j : ℕ, ∫ ω, X i ω ^ (2 * j + 1) ∂P = 0) (lam : ℝ) (hlam : 0 < lam) :
    ∫ ω, (∑ i, X i ω) ^ (2 * k) ∂P ≤
      ((2 * k).factorial : ℝ) / lam ^ (2 * k) * Real.exp ((d:ℝ) / 4 * lam ^ 2 / 2) := by
  have hG := l36_subG P X hXm hbdd hind hmom
  have hc : ((∑ i : Fin d, (‖(1/2:ℝ) - -(1/2)‖₊/2)^2 : NNReal) : ℝ) = (d:ℝ) / 4 := by
    push_cast
    simp [Real.norm_eq_abs]
    norm_num
    ring
  have h1 := hG.mgf_le lam
  have h2 := hG.mgf_le (-lam)
  rw [hc] at h1 h2
  have hi1 := hG.integrable_exp_mul lam
  have hi2 := hG.integrable_exp_mul (-lam)
  have hZm : Measurable (fun ω => ∑ i, X i ω) := Finset.measurable_sum _ (fun i _ => hXm i)
  have hZb : ∀ ω, |∑ i, X i ω| ≤ d := by
    intro ω
    calc |∑ i, X i ω| ≤ ∑ i, |X i ω| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin d, (1:ℝ) := by
          apply Finset.sum_le_sum; intro i _
          have := hbdd i ω
          rw [abs_le]; constructor <;> linarith [this.1, this.2]
      _ = d := by simp
  have hZint : Integrable (fun ω => (∑ i, X i ω) ^ (2 * k)) P := by
    refine Integrable.of_bound (C := (d:ℝ)^(2*k)) (hZm.pow_const _).aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall (fun ω => ?_)
    rw [norm_pow, Real.norm_eq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (hZb ω) _
  have hf : (0:ℝ) < ((2 * k).factorial : ℝ) := by positivity
  have hl : (0:ℝ) < lam ^ (2 * k) := by positivity
  have hpt : ∀ ω, (∑ i, X i ω) ^ (2 * k) ≤ ((2 * k).factorial : ℝ) / lam ^ (2 * k) *
      ((Real.exp (lam * ∑ i, X i ω) + Real.exp (-lam * ∑ i, X i ω)) / 2) := by
    intro ω
    have h := l36_cosh (lam * ∑ i, X i ω) k
    rw [Real.cosh_eq, mul_pow, div_le_iff₀ hf] at h
    rw [div_mul_eq_mul_div, le_div_iff₀ hl, neg_mul]
    calc (∑ i, X i ω) ^ (2 * k) * lam ^ (2 * k) = lam ^ (2 * k) * (∑ i, X i ω) ^ (2 * k) :=
          mul_comm _ _
      _ ≤ _ := h
      _ = _ := mul_comm _ _
  have hint2 : Integrable (fun ω => ((2 * k).factorial : ℝ) / lam ^ (2 * k) *
      ((Real.exp (lam * ∑ i, X i ω) + Real.exp (-lam * ∑ i, X i ω)) / 2)) P :=
    ((hi1.add hi2).div_const 2).const_mul _
  calc ∫ ω, (∑ i, X i ω) ^ (2 * k) ∂P
      ≤ ∫ ω, ((2 * k).factorial : ℝ) / lam ^ (2 * k) *
      ((Real.exp (lam * ∑ i, X i ω) + Real.exp (-lam * ∑ i, X i ω)) / 2) ∂P :=
        integral_mono hZint hint2 hpt
    _ = ((2 * k).factorial : ℝ) / lam ^ (2 * k) *
        ((mgf (fun ω => ∑ i, X i ω) P lam + mgf (fun ω => ∑ i, X i ω) P (-lam)) / 2) := by
        rw [integral_const_mul, integral_div, integral_add hi1 hi2]
        rfl
    _ ≤ ((2 * k).factorial : ℝ) / lam ^ (2 * k) * Real.exp ((d:ℝ) / 4 * lam ^ 2 / 2) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have h2' : mgf (fun ω => ∑ i, X i ω) P (-lam) ≤ Real.exp ((d:ℝ) / 4 * lam ^ 2 / 2) := by
          have := h2; rwa [neg_sq] at this
        linarith

lemma l36_exp_half : Real.exp (1 / 2) ≤ 2 := by
  have h1 := Real.exp_one_lt_d9
  have h2 : Real.exp (1 / 2) * Real.exp (1 / 2) = Real.exp 1 := by
    rw [← Real.exp_add]; norm_num
  have h3 := Real.exp_pos (1 / 2)
  nlinarith

lemma l36_fact (k : ℕ) (hk : 1 ≤ k) :
    ((2 * k).factorial : ℝ) * Real.exp ((k : ℝ) / 2) ≤ 2 * (2 * (k : ℝ) ^ 2) ^ k := by
  induction k, hk using Nat.le_induction with
  | base =>
    have := l36_exp_half
    norm_num [Nat.factorial]
    linarith
  | succ k hk ih =>
    have hk1 : (1:ℝ) ≤ k := by exact_mod_cast hk
    have hb : 2 * (k:ℝ) ^ k ≤ ((k:ℝ) + 1) ^ k := by
      have h := one_add_mul_le_pow (a := 1 / (k:ℝ)) (by
        have : (0:ℝ) ≤ 1 / (k:ℝ) := by positivity
        linarith) k
      have hkpos : (0:ℝ) < k := by linarith
      have e : ((k:ℝ) + 1) ^ k = (k:ℝ) ^ k * (1 + 1 / (k:ℝ)) ^ k := by
        rw [← mul_pow]; congr 1; field_simp
      rw [e]
      have : 1 + (k:ℝ) * (1 / (k:ℝ)) = 2 := by field_simp; norm_num
      rw [this] at h
      have hp : (0:ℝ) < (k:ℝ) ^ k := by positivity
      nlinarith
    have hc : 4 * (2 * (k:ℝ) ^ 2) ^ k ≤ (2 * ((k:ℝ) + 1) ^ 2) ^ k := by
      have e1 : (2 * ((k:ℝ) + 1) ^ 2) ^ k = 2 ^ k * (((k:ℝ) + 1) ^ k) ^ 2 := by
        rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm 2 k]
      have e2 : (2 * (k:ℝ) ^ 2) ^ k = 2 ^ k * ((k:ℝ) ^ k) ^ 2 := by
        rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm 2 k]
      rw [e1, e2]
      have h2 : (0:ℝ) < 2 ^ k := by positivity
      have h3 : 0 ≤ 2 * (k:ℝ) ^ k := by positivity
      have : (2 * (k:ℝ) ^ k) ^ 2 ≤ (((k:ℝ) + 1) ^ k) ^ 2 := pow_le_pow_left₀ h3 hb 2
      nlinarith
    have hfac : ((2 * (k + 1)).factorial : ℝ) =
        ((2 * (k:ℝ) + 2) * (2 * (k:ℝ) + 1)) * ((2 * k).factorial : ℝ) := by
      rw [show 2 * (k + 1) = (2 * k + 1) + 1 by ring, Nat.factorial_succ, Nat.factorial_succ]
      push_cast; ring
    have hexp : Real.exp (((k + 1 : ℕ) : ℝ) / 2) ≤ Real.exp ((k : ℝ) / 2) * 2 := by
      have : ((k + 1 : ℕ) : ℝ) / 2 = (k : ℝ) / 2 + 1 / 2 := by push_cast; ring
      rw [this, Real.exp_add]
      exact mul_le_mul_of_nonneg_left l36_exp_half (Real.exp_pos _).le
    rw [hfac]
    push_cast
    have hF : (0:ℝ) ≤ ((2 * k).factorial : ℝ) := by positivity
    have hP : (0:ℝ) ≤ (2 * (k:ℝ) ^ 2) ^ k := by positivity
    have hE : (0:ℝ) < Real.exp ((k : ℝ) / 2) := Real.exp_pos _
    have hE' : Real.exp (((k:ℝ) + 1) / 2) ≤ Real.exp ((k : ℝ) / 2) * 2 := by
      have := hexp; push_cast at this; exact this
    calc (2 * (k:ℝ) + 2) * (2 * (k:ℝ) + 1) * ((2 * k).factorial : ℝ) * Real.exp (((k:ℝ) + 1) / 2)
        ≤ (2 * (k:ℝ) + 2) * (2 * (k:ℝ) + 1) * ((2 * k).factorial : ℝ) * (Real.exp ((k : ℝ) / 2) * 2) := by
          apply mul_le_mul_of_nonneg_left hE' (by positivity)
      _ = 2 * ((2 * (k:ℝ) + 2) * (2 * (k:ℝ) + 1)) * (((2 * k).factorial : ℝ) * Real.exp ((k : ℝ) / 2)) := by ring
      _ ≤ 2 * ((2 * (k:ℝ) + 2) * (2 * (k:ℝ) + 1)) * (2 * (2 * (k:ℝ) ^ 2) ^ k) := by
          apply mul_le_mul_of_nonneg_left ih (by positivity)
      _ ≤ 2 * (2 * ((k:ℝ) + 1) ^ 2) * (4 * (2 * (k:ℝ) ^ 2) ^ k) := by
          have : (2 * (k:ℝ) + 2) * (2 * (k:ℝ) + 1) ≤ 4 * ((k:ℝ) + 1) ^ 2 := by nlinarith
          have h5 : 2 * ((2 * (k:ℝ) + 2) * (2 * (k:ℝ) + 1)) * (2 * (2 * (k:ℝ) ^ 2) ^ k)
              = 4 * ((2 * (k:ℝ) + 2) * (2 * (k:ℝ) + 1)) * (2 * (k:ℝ) ^ 2) ^ k := by ring
          rw [h5]
          nlinarith [mul_le_mul_of_nonneg_right this hP]
      _ ≤ 2 * (2 * ((k:ℝ) + 1) ^ 2) * (2 * ((k:ℝ) + 1) ^ 2) ^ k := by
          apply mul_le_mul_of_nonneg_left hc (by positivity)
      _ = 2 * (2 * ((k:ℝ) + 1) ^ 2) ^ (k + 1) := by ring

lemma l36_second_moment {d k : ℕ} (hd : 1 ≤ d) (hk : 1 ≤ k) (X : Fin d → Ω → ℝ)
    (hXm : ∀ i, Measurable (X i))
    (hbdd : ∀ i ω, X i ω ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2))
    (hind : iIndepFun X P)
    (hmom : ∀ i, ∀ j : ℕ, ∫ ω, X i ω ^ (2 * j + 1) ∂P = 0)
    (H : (Fin k → Fin d) → ℝ) (hH : ∀ α, |H α| ≤ 1) :
    ∫ ω, (∑ α : Fin k → Fin d, H α * ∏ j, X (α j) ω) ^ 2 ∂P ≤ 2 * ((d : ℝ) * k / 2) ^ k := by
  have h1 := l36_second P X hXm hbdd hind hmom H hH
  have hdr : (0:ℝ) < d := by exact_mod_cast hd
  have hkr : (0:ℝ) < k := by exact_mod_cast hk
  set lam := Real.sqrt (4 * k / d) with hlamdef
  have hlam : 0 < lam := Real.sqrt_pos.2 (by positivity)
  have h2 := l36_moment (k := k) P X hXm hbdd hind hmom lam hlam
  have hl2 : lam ^ 2 = 4 * k / d := Real.sq_sqrt (by positivity)
  have hl2k : lam ^ (2 * k) = (4 * k / d) ^ k := by rw [pow_mul, hl2]
  have hexp : (d:ℝ) / 4 * lam ^ 2 / 2 = k / 2 := by rw [hl2]; field_simp
  rw [hl2k, hexp] at h2
  have h3 := l36_fact k hk
  have e : ((4 * (k:ℝ) / d) ^ k)⁻¹ = ((d:ℝ) / (4 * k)) ^ k := by rw [← inv_pow, inv_div]
  have e2 : 2 * (k:ℝ) ^ 2 * ((d:ℝ) / (4 * k)) = d * k / 2 := by field_simp; ring
  calc _ ≤ _ := h1
    _ ≤ _ := h2
    _ = (((2 * k).factorial : ℝ) * Real.exp ((k:ℝ) / 2)) * ((d:ℝ) / (4 * k)) ^ k := by
        rw [div_eq_mul_inv, e]; ring
    _ ≤ (2 * (2 * (k:ℝ) ^ 2) ^ k) * ((d:ℝ) / (4 * k)) ^ k :=
        mul_le_mul_of_nonneg_right h3 (by positivity)
    _ = 2 * ((d : ℝ) * k / 2) ^ k := by
        rw [mul_assoc, ← mul_pow, e2]

end L36

theorem l36_main {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (d k : ℕ) (hd : 1 ≤ d) (hk : 1 ≤ k) (H : (Fin k → Fin d) → ℝ) (hH : ∀ α, |H α| ≤ 1)
    (X : Fin d → Ω → ℝ) (hXm : ∀ i, Measurable (X i)) (hind : iIndepFun X P)
    (hbdd : ∀ i ω, X i ω ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2))
    (hmom : ∀ i, ∀ j : ℕ, ∫ ω, X i ω ^ (2 * j + 1) ∂P = 0)
    (r : ℝ) (hr : 0 < r) :
    P {ω | Real.sqrt 2 * (r * Real.sqrt ((d : ℝ) * k / 2)) ^ k ≤
        |∑ α : Fin k → Fin d, H α * ∏ j, X (α j) ω|} ≤ ENNReal.ofReal (1 / r ^ (2 * k)) := by
  have hdr : (0:ℝ) < d := by exact_mod_cast hd
  have hkr : (0:ℝ) < k := by exact_mod_cast hk
  set S : Ω → ℝ := fun ω => ∑ α : Fin k → Fin d, H α * ∏ j, X (α j) ω with hS
  set t : ℝ := Real.sqrt 2 * (r * Real.sqrt ((d : ℝ) * k / 2)) ^ k with ht
  have ht0 : 0 < t := by positivity
  have hA : (0:ℝ) < ((d : ℝ) * k / 2) ^ k := by positivity
  have ht2 : t ^ 2 = 2 * r ^ (2 * k) * ((d : ℝ) * k / 2) ^ k := by
    have hq : ((r * Real.sqrt ((d : ℝ) * k / 2)) ^ k) ^ 2 = (r ^ 2 * ((d : ℝ) * k / 2)) ^ k := by
      rw [← pow_mul, mul_comm k 2, pow_mul, mul_pow, Real.sq_sqrt (by positivity)]
    rw [ht, mul_pow, Real.sq_sqrt (by norm_num), hq, mul_pow, ← pow_mul]
    ring
  have hSm : Measurable S :=
    Finset.measurable_sum _ (fun α _ => measurable_const.mul
      (Finset.measurable_prod _ (fun j _ => hXm (α j))))
  have hSb : ∀ ω, |S ω| ≤ (Fintype.card (Fin k → Fin d) : ℝ) := by
    intro ω
    calc |S ω| ≤ ∑ α : Fin k → Fin d, |H α * ∏ j, X (α j) ω| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _α : Fin k → Fin d, (1:ℝ) := by
          apply Finset.sum_le_sum; intro α _
          rw [abs_mul, Finset.abs_prod]
          have h1 : ∏ j, |X (α j) ω| ≤ 1 := by
            apply Finset.prod_le_one (fun _ _ => abs_nonneg _)
            intro j _
            have := hbdd (α j) ω
            rw [abs_le]; constructor <;> linarith [this.1, this.2]
          calc |H α| * ∏ j, |X (α j) ω| ≤ 1 * 1 :=
                mul_le_mul (hH α) h1 (Finset.prod_nonneg (fun _ _ => abs_nonneg _)) (by norm_num)
            _ = 1 := by norm_num
      _ = _ := by simp
  have hSint : Integrable (fun ω => S ω ^ 2) P := by
    refine Integrable.of_bound (C := (Fintype.card (Fin k → Fin d) : ℝ) ^ 2)
      (hSm.pow_const _).aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall (fun ω => ?_)
    rw [norm_pow, Real.norm_eq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (hSb ω) _
  have hmark := mul_meas_ge_le_integral_of_nonneg (μ := P) (f := fun ω => S ω ^ 2)
    (Filter.Eventually.of_forall (fun ω => sq_nonneg _)) hSint (t ^ 2)
  have hE := l36_second_moment P hd hk X hXm hbdd hind hmom H hH
  have hsub : {ω | t ≤ |S ω|} ⊆ {ω | t ^ 2 ≤ S ω ^ 2} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    calc t ^ 2 ≤ |S ω| ^ 2 := pow_le_pow_left₀ ht0.le hω 2
      _ = S ω ^ 2 := sq_abs _
  have hreal : P.real {ω | t ≤ |S ω|} ≤ 1 / r ^ (2 * k) := by
    have h1 : P.real {ω | t ≤ |S ω|} ≤ P.real {ω | t ^ 2 ≤ S ω ^ 2} :=
      measureReal_mono hsub
    have hr2 : (0:ℝ) < r ^ (2 * k) := by positivity
    have h2 : t ^ 2 * P.real {ω | t ^ 2 ≤ S ω ^ 2} ≤ 2 * ((d : ℝ) * k / 2) ^ k :=
      hmark.trans hE
    obtain ⟨p, hp⟩ : ∃ p, p = P.real {ω | t ^ 2 ≤ S ω ^ 2} := ⟨_, rfl⟩
    rw [← hp] at h1 h2
    rw [ht2] at h2
    have h3 : p ≤ 1 / r ^ (2 * k) := by
      rw [le_div_iff₀ hr2]
      have hpos : 0 < 2 * ((d : ℝ) * k / 2) ^ k := by positivity
      have h4 : (2 * ((d : ℝ) * k / 2) ^ k) * (p * r ^ (2 * k)) ≤
          (2 * ((d : ℝ) * k / 2) ^ k) * 1 := by nlinarith [h2]
      exact le_of_mul_le_mul_left h4 hpos
    exact h1.trans h3
  calc P {ω | t ≤ |S ω|} = ENNReal.ofReal (P.real {ω | t ≤ |S ω|}) :=
        (ofReal_measureReal).symm
    _ ≤ ENNReal.ofReal (1 / r ^ (2 * k)) := ENNReal.ofReal_le_ofReal hreal

noncomputable def gP0 (n : ℕ) : Measure (Qubits n) := (PMF.uniformOfFintype (Qubits n)).toMeasure

instance gP0_prob (n : ℕ) : IsProbabilityMeasure (gP0 n) := PMF.toMeasure.isProbabilityMeasure _

lemma gP0_single (n : ℕ) (b : Qubits n) : gP0 n {b} = ((2 ^ n : ℕ) : ENNReal)⁻¹ := by
  unfold gP0
  rw [PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton b), PMF.uniformOfFintype_apply]
  simp [Fintype.card_fun]

lemma grid_mem (n : ℕ) (b : Qubits n) : gridPoint n b ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2) := by
  have h1 : bitsToNat b < 2 ^ n := by
    have := (bitsEquivFin n b).2
    rwa [bitsEquivFin_apply] at this
  have h2 : (bitsToNat b : ℝ) + 1 ≤ 2 ^ n := by exact_mod_cast h1
  have hp : (0:ℝ) < 2 ^ n := by positivity
  have h3 : (0:ℝ) ≤ bitsToNat b := Nat.cast_nonneg _
  unfold gridPoint
  have e : ((2:ℝ) ^ (n + 1))⁻¹ = ((2:ℝ) ^ n)⁻¹ / 2 := by rw [pow_succ]; field_simp
  rw [e]
  constructor
  · have : 0 ≤ (bitsToNat b : ℝ) * ((2:ℝ) ^ n)⁻¹ := by positivity
    have : 0 ≤ ((2:ℝ) ^ n)⁻¹ / 2 := by positivity
    linarith
  · have : (bitsToNat b : ℝ) * ((2:ℝ) ^ n)⁻¹ ≤ 1 - ((2:ℝ) ^ n)⁻¹ := by
      rw [← div_eq_mul_inv, div_le_iff₀ hp]
      field_simp
      linarith
    have : (0:ℝ) < ((2:ℝ) ^ n)⁻¹ := by positivity
    linarith

lemma grid_sum_odd (n j : ℕ) : ∑ b : Qubits n, (gridPoint n b) ^ (2 * j + 1) = 0 := by
  set g : ℕ → ℝ := fun N => ((N : ℝ) * ((2:ℝ) ^ n)⁻¹ - 2⁻¹ + ((2:ℝ) ^ (n + 1))⁻¹) with hg
  have e : ∑ b : Qubits n, (gridPoint n b) ^ (2 * j + 1) =
      ∑ N ∈ Finset.range (2 ^ n), (g N) ^ (2 * j + 1) := by
    rw [← Fin.sum_univ_eq_sum_range (fun N => (g N) ^ (2 * j + 1)) (2 ^ n)]
    apply Fintype.sum_equiv (bitsEquivFin n)
    intro b
    simp only [bitsEquivFin_apply, hg, gridPoint]
  have hneg : ∀ N ∈ Finset.range (2 ^ n), g (2 ^ n - 1 - N) = - g N := by
    intro N hN
    have hN' : N < 2 ^ n := Finset.mem_range.1 hN
    have hc : ((2 ^ n - 1 - N : ℕ) : ℝ) = (2:ℝ) ^ n - 1 - N := by
      have : 1 + N ≤ 2 ^ n := by omega
      rw [Nat.sub_sub, Nat.cast_sub this]; push_cast; ring
    simp only [hg, hc]
    have hp : ((2:ℝ) ^ n) ≠ 0 := by positivity
    have e2 : ((2:ℝ) ^ (n + 1))⁻¹ = ((2:ℝ) ^ n)⁻¹ / 2 := by rw [pow_succ]; field_simp
    rw [e2]
    field_simp
    ring
  have h1 : ∑ N ∈ Finset.range (2 ^ n), (g N) ^ (2 * j + 1) =
      - ∑ N ∈ Finset.range (2 ^ n), (g N) ^ (2 * j + 1) := by
    calc ∑ N ∈ Finset.range (2 ^ n), (g N) ^ (2 * j + 1)
        = ∑ N ∈ Finset.range (2 ^ n), (g (2 ^ n - 1 - N)) ^ (2 * j + 1) :=
          (Finset.sum_range_reflect (fun N => (g N) ^ (2 * j + 1)) (2 ^ n)).symm
      _ = ∑ N ∈ Finset.range (2 ^ n), - (g N) ^ (2 * j + 1) := by
          apply Finset.sum_congr rfl
          intro N hN
          rw [hneg N hN, Odd.neg_pow ⟨j, rfl⟩]
      _ = _ := by rw [Finset.sum_neg_distrib]
  rw [e]
  linarith

lemma gP0_integral_odd (n j : ℕ) : ∫ b, (gridPoint n b) ^ (2 * j + 1) ∂(gP0 n) = 0 := by
  unfold gP0
  rw [PMF.integral_eq_sum]
  have : ∀ b : Qubits n, ((PMF.uniformOfFintype (Qubits n)) b).toReal = ((2 ^ n : ℕ) : ℝ)⁻¹ := by
    intro b
    simp [PMF.uniformOfFintype_apply]
  simp only [this, smul_eq_mul]
  rw [← Finset.mul_sum, grid_sum_odd, mul_zero]

noncomputable def gP (d n : ℕ) : Measure (Fin d → Qubits n) := Measure.pi (fun _ => gP0 n)

instance gP_prob (d n : ℕ) : IsProbabilityMeasure (gP d n) := by unfold gP; infer_instance

lemma gP_single (d n : ℕ) (ω : Fin d → Qubits n) : gP d n {ω} = (((2 ^ n : ℕ) : ENNReal)⁻¹) ^ d := by
  unfold gP
  rw [Measure.pi_singleton]
  simp [gP0_single]

lemma gP_finset (d n : ℕ) (S : Finset (Fin d → Qubits n)) :
    gP d n (S : Set (Fin d → Qubits n)) = (S.card : ENNReal) * (((2 ^ n : ℕ) : ENNReal)⁻¹) ^ d := by
  rw [← sum_measure_singleton]
  simp [gP_single]

lemma gP_meas (d n : ℕ) (i : Fin d) : Measurable (fun ω : Fin d → Qubits n => gridPoint n (ω i)) :=
  (measurable_of_finite (gridPoint n)).comp (measurable_pi_apply i)

lemma gP_indep (d n : ℕ) :
    iIndepFun (fun (i : Fin d) (ω : Fin d → Qubits n) => gridPoint n (ω i)) (gP d n) :=
  iIndepFun_pi (μ := fun _ : Fin d => gP0 n) (X := fun _ => gridPoint n)
    (fun i => (measurable_of_finite (gridPoint n)).aemeasurable)

lemma gP_mom (d n : ℕ) (i : Fin d) (j : ℕ) :
    ∫ ω, (gridPoint n (ω i)) ^ (2 * j + 1) ∂(gP d n) = 0 := by
  have hmp := measurePreserving_eval (fun _ : Fin d => gP0 n) i
  have h := integral_map (μ := gP d n) (φ := fun ω : Fin d → Qubits n => ω i)
    (f := fun b : Qubits n => (gridPoint n b) ^ (2 * j + 1))
    (measurable_pi_apply i).aemeasurable (measurable_of_finite _).aestronglyMeasurable
  have hm : (gP d n).map (fun ω : Fin d → Qubits n => ω i) = gP0 n := hmp.map_eq
  rw [hm] at h
  rw [← h, gP0_integral_odd]


noncomputable def t24T {d : ℕ} (f : (Fin d → ℝ) → ℝ) (k : ℕ) (y : Fin d → ℝ) : ℝ :=
  ∑ α : Fin k → Fin d, (∏ j, y (α j)) * partialAlpha f k α 0 / (k.factorial : ℝ)

noncomputable def t24M (m k : ℕ) : ℝ :=
  ∑ ℓ ∈ Finset.Icc (-(m : ℤ)) m, centralCoeff m ℓ * (ℓ : ℝ) ^ k

lemma t24_smul {d : ℕ} (f : (Fin d → ℝ) → ℝ) (k : ℕ) (a : ℝ) (y : Fin d → ℝ) :
    t24T f k (a • y) = a ^ k * t24T f k y := by
  unfold t24T
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro α _
  have : ∏ j, (a • y) (α j) = a ^ k * ∏ j, y (α j) := by
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [this]; ring

lemma t24_hasSum {d : ℕ} (m : ℕ) (f : (Fin d → ℝ) → ℝ) (han : IsTaylorRep f 0) (y : Fin d → ℝ) :
    HasSum (fun k => t24M m k * t24T f k y) (centralDiff m f y) := by
  have h1 : ∀ ℓ : ℤ, HasSum (fun k => (ℓ:ℝ) ^ k * t24T f k y) (f ((ℓ:ℝ) • y)) := by
    intro ℓ
    have := han ((ℓ:ℝ) • y)
    rw [zero_add] at this
    convert this using 2 with k
    exact (t24_smul f k (ℓ:ℝ) y).symm
  have h2 := hasSum_sum (s := Finset.Icc (-(m : ℤ)) m)
    (fun ℓ _ => (h1 ℓ).mul_left (centralCoeff m ℓ))
  have e : (fun k => t24M m k * t24T f k y) =
      fun k => ∑ ℓ ∈ Finset.Icc (-(m : ℤ)) m, centralCoeff m ℓ * ((ℓ:ℝ) ^ k * t24T f k y) := by
    funext k
    unfold t24M
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro ℓ _
    ring
  have e2 : centralDiff m f y =
      ∑ ℓ ∈ Finset.Icc (-(m : ℤ)) m, centralCoeff m ℓ * f ((ℓ:ℝ) • y) := rfl
  rw [e, e2]
  exact h2


lemma t24_fderiv {d : ℕ} (f : (Fin d → ℝ) → ℝ) (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (y : Fin d → ℝ) : t24T f 1 y = fderiv ℝ f 0 y := by
  have hd : DifferentiableAt ℝ f 0 := (hf.differentiable (by simp)).differentiableAt
  unfold t24T partialAlpha
  simp only [iteratedFDeriv_one_apply, Nat.factorial_one, Nat.cast_one, div_one]
  rw [← Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Fin d)).symm
    (fun i : Fin d => y i * (fderiv ℝ f 0) (Pi.single i 1)) _ (fun i => by simp)]
  conv_rhs => rw [← Finset.univ_sum_single y]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  have : (Pi.single i (y i) : Fin d → ℝ) = y i • (Pi.single i 1 : Fin d → ℝ) := by
    ext j
    by_cases h : j = i <;> simp [Pi.single_apply, h]
  rw [this, map_smul, smul_eq_mul]


lemma t24_split (m : ℕ) (hm : 1 ≤ m) {d : ℕ} (f : (Fin d → ℝ) → ℝ)
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) (han : IsTaylorRep f 0) (y : Fin d → ℝ) :
    HasSum (fun k => t24M m (k + (2*m+1)) * t24T f (k + (2*m+1)) y)
      (centralDiff m f y - fderiv ℝ f 0 y) := by
  have h := (hasSum_nat_add_iff' (2*m+1)).mpr (t24_hasSum m f han y)
  have hsum : ∑ i ∈ Finset.range (2*m+1), t24M m i * t24T f i y = fderiv ℝ f 0 y := by
    rw [Finset.sum_eq_single 1]
    · have := qg_moments m 1 (by omega)
      unfold t24M
      rw [this, if_pos rfl, one_mul]
      exact t24_fderiv f hf y
    · intro i hi hne
      have hi' : i ≤ 2 * m := by simp at hi; omega
      unfold t24M
      rw [qg_moments m i hi', if_neg hne, zero_mul]
    · intro h1
      simp at h1
      omega
  rw [hsum] at h
  exact h

lemma t24_det (m : ℕ) (hm : 1 ≤ m) {d : ℕ} (f : (Fin d → ℝ) → ℝ)
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) (han : IsTaylorRep f 0) (y : Fin d → ℝ)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hgood : ∀ k, 2 * m + 1 ≤ k → |t24M m k * t24T f k y| ≤ q ^ k) :
    |fderiv ℝ f 0 y - centralDiff m f y| ≤ ∑' k : ℕ, q ^ (2 * m + 1 + k) := by
  have h := t24_split m hm f hf han y
  have hg : HasSum (fun k : ℕ => q ^ (2 * m + 1 + k)) (∑' k : ℕ, q ^ (2 * m + 1 + k)) := by
    have : Summable (fun k : ℕ => q ^ (2 * m + 1 + k)) := by
      simp_rw [pow_add]
      exact (summable_geometric_of_lt_one hq0 hq1).mul_left _
    exact this.hasSum
  have := HasSum.norm_le_of_bounded h hg (fun k => by
    rw [Real.norm_eq_abs]
    rw [add_comm k (2*m+1)]
    exact hgood _ (by omega))
  rw [Real.norm_eq_abs] at this
  rw [abs_sub_comm]
  exact this


lemma t24_beta (m k : ℕ) (hm : 1 ≤ m) (hk : 2 * m + 1 ≤ k) :
    6 * Real.sqrt 2 * Real.exp (-(7 * (m:ℝ) / 6)) * Real.sqrt m ≤ Real.sqrt (2 * Real.pi * k) := by
  have hmr : (1:ℝ) ≤ m := by exact_mod_cast hm
  have hkr : (2:ℝ) * m + 1 ≤ k := by exact_mod_cast hk
  apply Real.le_sqrt_of_sq_le
  have hE : Real.exp (-(7 * (m:ℝ) / 6)) ^ 2 ≤ 1 / 7 := by
    rw [← Real.exp_nat_mul]
    have h1 : Real.exp (((2:ℕ):ℝ) * (-(7 * (m:ℝ) / 6))) ≤ Real.exp (-2) := by
      apply Real.exp_le_exp.2
      push_cast
      nlinarith
    have h2 : Real.exp (-2) = (Real.exp 1)⁻¹ ^ 2 := by
      rw [← Real.exp_neg, ← Real.exp_nat_mul]; norm_num
    have h3 := Real.exp_one_gt_d9
    have h4 : (Real.exp 1)⁻¹ ≤ 1 / 2.7182818283 := by
      rw [one_div]; exact inv_anti₀ (by norm_num) h3.le
    have h5 : (Real.exp 1)⁻¹ ^ 2 ≤ (1 / 2.7182818283) ^ 2 :=
      pow_le_pow_left₀ (by positivity) h4 2
    have h6 : ((1:ℝ) / 2.7182818283) ^ 2 ≤ 1 / 7 := by norm_num
    linarith
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsm : Real.sqrt (m:ℝ) ^ 2 = m := Real.sq_sqrt (by positivity)
  have hpi := Real.pi_gt_three
  have hmul : (6 * Real.sqrt 2 * Real.exp (-(7 * (m:ℝ) / 6)) * Real.sqrt m) ^ 2 =
      72 * Real.exp (-(7 * (m:ℝ) / 6)) ^ 2 * m := by
    rw [mul_pow, mul_pow, mul_pow, hs2, hsm]; ring
  rw [hmul]
  have hE0 : 0 ≤ Real.exp (-(7 * (m:ℝ) / 6)) ^ 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_right hE (by linarith : (0:ℝ) ≤ m)]


lemma t24_arith (m k : ℕ) (hm : 1 ≤ m) (hk : 2 * m + 1 ≤ k) (A : ℝ) (hA : 0 ≤ A) (Mk Tk : ℝ)
    (hM : |Mk| ≤ 6 * Real.exp (-(7 * (m:ℝ) / 6)) * (m:ℝ) ^ k * Real.sqrt m)
    (hT : |Tk| ≤ Real.sqrt 2 * (2 * Real.sqrt 2 * A) ^ k * ((k:ℝ) ^ k / (k.factorial : ℝ))) :
    |Mk * Tk| ≤ (8 * A * m) ^ k := by
  have hmr : (1:ℝ) ≤ m := by exact_mod_cast hm
  have hkpos : (0:ℝ) < k := by
    have : (0:ℝ) < 2 * m + 1 := by linarith
    have hkr : (2:ℝ) * m + 1 ≤ k := by exact_mod_cast hk
    linarith
  have hsq : Real.sqrt (2 * Real.pi * k) > 0 := by positivity
  have hst := Stirling.le_factorial_stirling k
  have hfk : (k:ℝ) ^ k / (k.factorial : ℝ) ≤ Real.exp 1 ^ k / Real.sqrt (2 * Real.pi * k) := by
    rw [div_le_div_iff₀ (by positivity) hsq]
    rw [div_pow] at hst
    have he : (0:ℝ) < Real.exp 1 ^ k := by positivity
    have := mul_le_mul_of_nonneg_right hst he.le
    have e2 : Real.sqrt (2 * Real.pi * k) * ((k:ℝ) ^ k / Real.exp 1 ^ k) * Real.exp 1 ^ k =
        Real.sqrt (2 * Real.pi * k) * (k:ℝ) ^ k := by field_simp
    rw [e2] at this
    linarith
  have hE0 : 0 < Real.exp (-(7 * (m:ℝ) / 6)) := Real.exp_pos _
  have hβ : 6 * Real.sqrt 2 * Real.exp (-(7 * (m:ℝ) / 6)) * Real.sqrt m / Real.sqrt (2 * Real.pi * k) ≤ 1 := by
    rw [div_le_one hsq]
    exact t24_beta m k hm hk
  have hbase : 2 * Real.sqrt 2 * Real.exp 1 ≤ 8 := by
    have h1 : Real.sqrt 2 ≤ 1.4143 := by
      rw [Real.sqrt_le_left (by norm_num)]; norm_num
    have h2 := Real.exp_one_lt_d9
    have h3 := Real.exp_pos 1
    have h4 := Real.sqrt_nonneg 2
    nlinarith
  have hmT : 0 ≤ (m:ℝ) ^ k := by positivity
  calc |Mk * Tk| = |Mk| * |Tk| := abs_mul _ _
    _ ≤ (6 * Real.exp (-(7 * (m:ℝ) / 6)) * (m:ℝ) ^ k * Real.sqrt m) *
        (Real.sqrt 2 * (2 * Real.sqrt 2 * A) ^ k * ((k:ℝ) ^ k / (k.factorial : ℝ))) :=
        mul_le_mul hM hT (abs_nonneg _) (by positivity)
    _ ≤ (6 * Real.exp (-(7 * (m:ℝ) / 6)) * (m:ℝ) ^ k * Real.sqrt m) *
        (Real.sqrt 2 * (2 * Real.sqrt 2 * A) ^ k * (Real.exp 1 ^ k / Real.sqrt (2 * Real.pi * k))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_left hfk (by positivity)
    _ = (6 * Real.sqrt 2 * Real.exp (-(7 * (m:ℝ) / 6)) * Real.sqrt m / Real.sqrt (2 * Real.pi * k)) *
        (2 * Real.sqrt 2 * Real.exp 1 * A * m) ^ k := by
        rw [mul_pow, mul_pow, mul_pow]; ring
    _ ≤ 1 * (8 * A * m) ^ k := by
        apply mul_le_mul hβ _ (by positivity) (by norm_num)
        apply pow_le_pow_left₀ (by positivity)
        have : 2 * Real.sqrt 2 * Real.exp 1 * A * m = (2 * Real.sqrt 2 * Real.exp 1) * (A * m) := by ring
        rw [this, show 8 * A * (m:ℝ) = 8 * (A * m) by ring]
        exact mul_le_mul_of_nonneg_right hbase (by positivity)
    _ = _ := one_mul _


lemma t24_Mbound (m k : ℕ) (hm : 1 ≤ m) (hk : 2 * m + 1 ≤ k) :
    |t24M m k| ≤ 6 * Real.exp (-(7 * (m:ℝ) / 6)) * (m:ℝ) ^ k * Real.sqrt m := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have h := l34_main m k' hm (by omega)
  have hmr : (0:ℝ) < m := by exact_mod_cast hm
  have e : (m:ℝ) ^ ((k':ℝ) + 3 / 2) = (m:ℝ) ^ (k' + 1) * Real.sqrt m := by
    have : ((k':ℝ) + 3/2) = ((k' + 1 : ℕ) : ℝ) + 1/2 := by push_cast; ring
    rw [this, Real.rpow_add hmr, Real.rpow_natCast, ← Real.sqrt_eq_rpow]
  rw [e] at h
  unfold t24M
  calc |∑ ℓ ∈ Finset.Icc (-(m : ℤ)) m, centralCoeff m ℓ * (ℓ : ℝ) ^ (k' + 1)|
      ≤ ∑ ℓ ∈ Finset.Icc (-(m : ℤ)) m, |centralCoeff m ℓ * (ℓ : ℝ) ^ (k' + 1)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := h
    _ = _ := by ring

lemma t24_good_k (m n d : ℕ) (hm : 1 ≤ m) (R c : ℝ) (hR : 0 < R) (hc : 0 < c)
    (f : (Fin d → ℝ) → ℝ)
    (hder : ∀ k : ℕ, 1 ≤ k → ∀ α : Fin k → Fin d, |partialAlpha f k α 0| ≤ c ^ k * Real.sqrt k ^ k)
    (k : ℕ) (hk : 2 * m + 1 ≤ k) (x : Fin d → Qubits n)
    (hx : ¬ (Real.sqrt 2 * (4 * Real.sqrt ((d:ℝ) * k / 2)) ^ k ≤
      |∑ α : Fin k → Fin d, (partialAlpha f k α 0 / (c ^ k * Real.sqrt k ^ k)) *
        ∏ j, gridPoint n (x (α j))|)) :
    |t24M m k * t24T f k (R • gridVec x)| ≤ (8 * R * c * m * Real.sqrt d) ^ k := by
  have hkpos : (0:ℝ) < k := by
    have : (0:ℝ) ≤ 2 * m := by positivity
    have hkr : (2:ℝ) * m + 1 ≤ k := by exact_mod_cast hk
    linarith
  have hden : 0 < c ^ k * Real.sqrt k ^ k := by positivity
  set S : ℝ := ∑ α : Fin k → Fin d, (partialAlpha f k α 0 / (c ^ k * Real.sqrt k ^ k)) *
        ∏ j, gridPoint n (x (α j)) with hS
  have hSb : |S| < Real.sqrt 2 * (4 * Real.sqrt ((d:ℝ) * k / 2)) ^ k := not_le.mp hx
  have hT : t24T f k (R • gridVec x) = (R * c * Real.sqrt k) ^ k / (k.factorial : ℝ) * S := by
    unfold t24T
    rw [hS, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro α _
    have h1 : ∏ j, (R • gridVec x) (α j) = R ^ k * ∏ j, gridPoint n (x (α j)) := by
      simp only [Pi.smul_apply, gridVec, smul_eq_mul]
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [h1]
    field_simp
    ring
  have hTb : |t24T f k (R • gridVec x)| ≤
      Real.sqrt 2 * (2 * Real.sqrt 2 * (R * c * Real.sqrt d)) ^ k * ((k:ℝ) ^ k / (k.factorial : ℝ)) := by
    rw [hT, abs_mul, abs_div, abs_of_pos (by positivity : (0:ℝ) < (R * c * Real.sqrt k) ^ k),
      abs_of_pos (by positivity : (0:ℝ) < (k.factorial : ℝ))]
    have hK : (R * c * Real.sqrt k) ^ k / (k.factorial : ℝ) * |S| ≤
        (R * c * Real.sqrt k) ^ k / (k.factorial : ℝ) *
          (Real.sqrt 2 * (4 * Real.sqrt ((d:ℝ) * k / 2)) ^ k) :=
      mul_le_mul_of_nonneg_left hSb.le (by positivity)
    refine hK.trans (le_of_eq ?_)
    have e1 : Real.sqrt k * (4 * Real.sqrt ((d:ℝ) * k / 2)) = 2 * Real.sqrt 2 * Real.sqrt d * k := by
      have hd0 : (0:ℝ) ≤ d := Nat.cast_nonneg d
      have : Real.sqrt ((d:ℝ) * k / 2) = Real.sqrt d * Real.sqrt k / Real.sqrt 2 := by
        rw [Real.sqrt_div (by positivity), Real.sqrt_mul hd0]
      rw [this]
      have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
      have hsk : Real.sqrt k * Real.sqrt k = k := Real.mul_self_sqrt hkpos.le
      have hs2p : 0 < Real.sqrt 2 := by positivity
      rw [mul_div_assoc', mul_div_assoc', div_eq_iff hs2p.ne']
      calc Real.sqrt k * (4 * (Real.sqrt d * Real.sqrt k)) = 4 * Real.sqrt d * (Real.sqrt k * Real.sqrt k) := by ring
        _ = 4 * Real.sqrt d * k := by rw [hsk]
        _ = 2 * Real.sqrt 2 * Real.sqrt d * k * Real.sqrt 2 := by
          calc 4 * Real.sqrt d * (k:ℝ) = 2 * (Real.sqrt 2 * Real.sqrt 2) * Real.sqrt d * k := by rw [hs2]; ring
            _ = _ := by ring
    have e2 : (R * c * Real.sqrt k) ^ k * (4 * Real.sqrt ((d:ℝ) * k / 2)) ^ k =
        (2 * Real.sqrt 2 * (R * c * Real.sqrt d) * k) ^ k := by
      rw [← mul_pow]
      congr 1
      calc R * c * Real.sqrt k * (4 * Real.sqrt ((d:ℝ) * k / 2))
          = R * c * (Real.sqrt k * (4 * Real.sqrt ((d:ℝ) * k / 2))) := by ring
        _ = _ := by rw [e1]; ring
    calc (R * c * Real.sqrt k) ^ k / (k.factorial : ℝ) *
          (Real.sqrt 2 * (4 * Real.sqrt ((d:ℝ) * k / 2)) ^ k)
        = Real.sqrt 2 * ((R * c * Real.sqrt k) ^ k * (4 * Real.sqrt ((d:ℝ) * k / 2)) ^ k) /
          (k.factorial : ℝ) := by ring
      _ = _ := by rw [e2, mul_pow]; ring
  have hMb := t24_Mbound m k hm hk
  have := t24_arith m k hm hk (R * c * Real.sqrt d) (by positivity) _ _ hMb hTb
  refine this.trans (le_of_eq ?_)
  ring


lemma gP_card (d n : ℕ) (F : Finset (Fin d → Qubits n)) (p : ℝ) (hp : 0 ≤ p)
    (h : gP d n (F : Set (Fin d → Qubits n)) ≤ ENNReal.ofReal p) :
    (F.card : ℝ) ≤ p * ((2:ℝ) ^ n) ^ d := by
  rw [gP_finset] at h
  have e : (F.card : ENNReal) * (((2 ^ n : ℕ) : ENNReal)⁻¹) ^ d =
      ENNReal.ofReal ((F.card : ℝ) * (((2:ℝ) ^ n)⁻¹) ^ d) := by
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast,
      ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_inv_of_pos (by positivity)]
    simp
  rw [e, ENNReal.ofReal_le_ofReal_iff hp] at h
  have hp2 : (0:ℝ) < ((2:ℝ) ^ n) ^ d := by positivity
  rw [inv_pow] at h
  rw [← div_eq_mul_inv, div_le_iff₀ hp2] at h
  exact h

lemma t24_bad_measure (d n : ℕ) (hd : 1 ≤ d) (c : ℝ) (hc : 0 < c) (f : (Fin d → ℝ) → ℝ)
    (hder : ∀ k : ℕ, 1 ≤ k → ∀ α : Fin k → Fin d, |partialAlpha f k α 0| ≤ c ^ k * Real.sqrt k ^ k)
    (k : ℕ) (hk : 1 ≤ k) :
    gP d n {x : Fin d → Qubits n | Real.sqrt 2 * (4 * Real.sqrt ((d:ℝ) * k / 2)) ^ k ≤
      |∑ α : Fin k → Fin d, (partialAlpha f k α 0 / (c ^ k * Real.sqrt k ^ k)) *
        ∏ j, gridPoint n (x (α j))|} ≤ ENNReal.ofReal (1 / 4 ^ (2 * k)) := by
  have hden : 0 < c ^ k * Real.sqrt k ^ k := by
    have : (0:ℝ) < k := by exact_mod_cast hk
    positivity
  have hH : ∀ α : Fin k → Fin d, |partialAlpha f k α 0 / (c ^ k * Real.sqrt k ^ k)| ≤ 1 := by
    intro α
    rw [abs_div, abs_of_pos hden, div_le_one hden]
    exact hder k hk α
  have := l36_main (gP d n) d k hd hk (fun α => partialAlpha f k α 0 / (c ^ k * Real.sqrt k ^ k)) hH
    (fun i ω => gridPoint n (ω i)) (gP_meas d n) (gP_indep d n)
    (fun i ω => grid_mem n (ω i)) (fun i j => gP_mom d n i j) 4 (by norm_num)
  simpa using this


lemma t24_e (m i : ℕ) : ((1:ℝ) / 4 ^ (2 * (i + (2 * m + 1)))) = (1 / 16) ^ (2 * m + 1) * (1 / 16) ^ i := by
  have h : (4:ℝ) ^ (2 * (i + (2 * m + 1))) = 16 ^ (i + (2 * m + 1)) := by
    rw [pow_mul]; norm_num
  rw [h, ← one_div_pow, ← pow_add, add_comm]

lemma t24_geo (m : ℕ) (hm : 1 ≤ m) :
    ∑' i : ℕ, ((1:ℝ) / 4 ^ (2 * (i + (2 * m + 1)))) ≤ 1 / 1000 := by
  have e := t24_e m
  simp_rw [e]
  rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
  have h3 : ((1:ℝ) / 16) ^ (2 * m + 1) ≤ (1 / 16) ^ 3 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  calc (1 / 16 : ℝ) ^ (2 * m + 1) * (1 - 1 / 16)⁻¹ ≤ (1 / 16) ^ 3 * (1 - 1 / 16)⁻¹ :=
        mul_le_mul_of_nonneg_right h3 (by norm_num)
    _ ≤ 1 / 1000 := by norm_num

lemma t24_union (m n d : ℕ) (hm : 1 ≤ m) (hd : 1 ≤ d) (c : ℝ) (hc : 0 < c) (f : (Fin d → ℝ) → ℝ)
    (hder : ∀ k : ℕ, 1 ≤ k → ∀ α : Fin k → Fin d, |partialAlpha f k α 0| ≤ c ^ k * Real.sqrt k ^ k) :
    gP d n {x : Fin d → Qubits n | ∃ k : ℕ, 2 * m + 1 ≤ k ∧ Real.sqrt 2 * (4 * Real.sqrt ((d:ℝ) * k / 2)) ^ k ≤
      |∑ α : Fin k → Fin d, (partialAlpha f k α 0 / (c ^ k * Real.sqrt k ^ k)) *
        ∏ j, gridPoint n (x (α j))|} ≤ ENNReal.ofReal (1 / 1000) := by
  have hset : {x : Fin d → Qubits n | ∃ k : ℕ, 2 * m + 1 ≤ k ∧ Real.sqrt 2 * (4 * Real.sqrt ((d:ℝ) * k / 2)) ^ k ≤
      |∑ α : Fin k → Fin d, (partialAlpha f k α 0 / (c ^ k * Real.sqrt k ^ k)) *
        ∏ j, gridPoint n (x (α j))|} =
      ⋃ i : ℕ, {x : Fin d → Qubits n | Real.sqrt 2 * (4 * Real.sqrt ((d:ℝ) * ((i + (2 * m + 1) : ℕ) : ℝ) / 2)) ^ (i + (2 * m + 1)) ≤
      |∑ α : Fin (i + (2 * m + 1)) → Fin d, (partialAlpha f (i + (2 * m + 1)) α 0 /
          (c ^ (i + (2 * m + 1)) * Real.sqrt ((i + (2 * m + 1) : ℕ) : ℝ) ^ (i + (2 * m + 1)))) *
        ∏ j, gridPoint n (x (α j))|} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨k, hk, h⟩
      obtain ⟨i, rfl⟩ : ∃ i, k = i + (2 * m + 1) := ⟨k - (2 * m + 1), by omega⟩
      exact ⟨i, h⟩
    · rintro ⟨i, h⟩
      exact ⟨i + (2 * m + 1), by omega, h⟩
  rw [hset]
  refine (measure_iUnion_le _).trans ?_
  have hsum : Summable (fun i : ℕ => ((1:ℝ) / 4 ^ (2 * (i + (2 * m + 1))))) := by
    have e := t24_e m
    simp_rw [e]
    exact (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  calc ∑' i : ℕ, gP d n _ ≤ ∑' i : ℕ, ENNReal.ofReal ((1:ℝ) / 4 ^ (2 * (i + (2 * m + 1)))) :=
        ENNReal.tsum_le_tsum (fun i => t24_bad_measure d n hd c hc f hder (i + (2 * m + 1)) (by omega))
    _ = ENNReal.ofReal (∑' i : ℕ, ((1:ℝ) / 4 ^ (2 * (i + (2 * m + 1))))) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun i => by positivity) hsum).symm
    _ ≤ ENNReal.ofReal (1 / 1000) := ENNReal.ofReal_le_ofReal (t24_geo m hm)


theorem solution (d n m : ℕ) (hm : 1 ≤ m) (R c : ℝ) (hR : 0 < R)
    (f : (Fin d → ℝ) → ℝ) (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) (han : IsTaylorRep f 0)
    (hder : ∀ k : ℕ, 1 ≤ k → ∀ α : Fin k → Fin d, |partialAlpha f k α 0| ≤ c ^ k * Real.sqrt k ^ k)
    (hq : 8 * R * c * m * Real.sqrt d < 1) :
    ((Finset.univ.filter fun x : Fin d → Qubits n =>
        ¬ |fderiv ℝ f 0 (R • gridVec x) - centralDiff m f (R • gridVec x)| ≤
          ∑' k : ℕ, (8 * R * c * m * Real.sqrt d) ^ (2 * m + 1 + k)).card : ℝ) ≤
      (2 ^ n : ℝ) ^ d / 1000 := by
  by_cases hdeg : d = 0 ∨ c = 0
  · -- degenerate case: all Taylor terms of order ≥ 1 vanish
    have hT0 : ∀ k : ℕ, 1 ≤ k → ∀ y : Fin d → ℝ, t24T f k y = 0 := by
      intro k hk y
      unfold t24T
      apply Finset.sum_eq_zero
      intro α _
      rcases hdeg with h0 | h0
      · subst h0
        exact (α ⟨0, hk⟩).elim0
      · have := hder k hk α
        rw [h0, zero_pow (by omega), zero_mul] at this
        have h2 : partialAlpha f k α 0 = 0 := abs_nonpos_iff.1 this
        rw [h2]; simp
    have hq0 : 8 * R * c * m * Real.sqrt d = 0 := by
      rcases hdeg with h0 | h0
      · subst h0; simp
      · rw [h0]; simp
    have hempty : Finset.univ.filter (fun x : Fin d → Qubits n =>
        ¬ |fderiv ℝ f 0 (R • gridVec x) - centralDiff m f (R • gridVec x)| ≤
          ∑' k : ℕ, (8 * R * c * m * Real.sqrt d) ^ (2 * m + 1 + k)) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro x _
      rw [not_not]
      apply t24_det m hm f hf han (R • gridVec x) _ (by rw [hq0]) hq
      intro k hk
      rw [hT0 k (by omega), mul_zero, abs_zero, hq0, zero_pow (by omega)]
    rw [hempty]
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity
  · push_neg at hdeg
    obtain ⟨hd0, hc0⟩ := hdeg
    have hd : 1 ≤ d := Nat.one_le_iff_ne_zero.2 hd0
    have hc : 0 < c := by
      by_contra hneg
      have hcn : c < 0 := lt_of_le_of_ne (not_lt.1 hneg) hc0
      have := hder 1 le_rfl (fun _ => ⟨0, hd⟩)
      simp at this
      linarith [abs_nonneg (partialAlpha f 1 (fun _ => (⟨0, hd⟩ : Fin d)) 0)]
    have hq0 : 0 ≤ 8 * R * c * m * Real.sqrt d := by positivity
    set F := Finset.univ.filter (fun x : Fin d → Qubits n =>
        ¬ |fderiv ℝ f 0 (R • gridVec x) - centralDiff m f (R • gridVec x)| ≤
          ∑' k : ℕ, (8 * R * c * m * Real.sqrt d) ^ (2 * m + 1 + k)) with hF
    have hsub : (F : Set (Fin d → Qubits n)) ⊆ {x : Fin d → Qubits n | ∃ k : ℕ, 2 * m + 1 ≤ k ∧
        Real.sqrt 2 * (4 * Real.sqrt ((d:ℝ) * k / 2)) ^ k ≤
        |∑ α : Fin k → Fin d, (partialAlpha f k α 0 / (c ^ k * Real.sqrt k ^ k)) *
          ∏ j, gridPoint n (x (α j))|} := by
      intro x hx
      by_contra hno
      have hx' := (Finset.mem_filter.1 (Finset.mem_coe.1 hx)).2
      apply hx'
      apply t24_det m hm f hf han (R • gridVec x) _ hq0 hq
      intro k hk
      apply t24_good_k m n d hm R c hR hc f hder k hk x
      intro hbad
      exact hno ⟨k, hk, hbad⟩
    have hmeas : gP d n (F : Set (Fin d → Qubits n)) ≤ ENNReal.ofReal (1 / 1000) :=
      (measure_mono hsub).trans (t24_union m n d hm hd c hc f hder)
    have := gP_card d n F (1 / 1000) (by norm_num) hmeas
    calc (F.card : ℝ) ≤ 1 / 1000 * ((2:ℝ) ^ n) ^ d := this
      _ = (2 ^ n : ℝ) ^ d / 1000 := by ring

