-- Prove2me | solution 1 for QGradGAW.Smooth.lemma_34
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T17:55:12.694555+00:00
-- url     : https://prove2.me/submissions/419c2078-0977-4ee6-bf0c-d786cf67705d

import Mathlib
import Definitions.Def_QGradGAW_Smooth_Setting

set_option autoImplicit false
open QGradGAW.Smooth

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

theorem solution (m k : ℕ) (hm : 1 ≤ m) (hk : 2 * m ≤ k) :
    ∑ ℓ ∈ Finset.Icc (-(m : ℤ)) m, |centralCoeff m ℓ * (ℓ : ℝ) ^ (k + 1)| ≤
      6 * Real.exp (-(7 * (m : ℝ) / 6)) * (m : ℝ) ^ ((k : ℝ) + 3 / 2) := by
  rw [l34_reindex]
  rcases (show m = 1 ∨ 2 ≤ m by omega) with rfl | h2
  · exact l34_m1 k hk
  · exact (l34_range_bound m k hk).trans (l34_final m k h2 hk)
