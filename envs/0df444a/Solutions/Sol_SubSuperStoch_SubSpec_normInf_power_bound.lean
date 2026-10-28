-- Prove2me | solution 1 for SubSuperStoch.SubSpec.normInf_power_bound
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-10-26T10:38:52.537463+00:00
-- url     : https://prove2.me/submissions/a0142e75-d21d-4b6e-a663-9c472de7a9b0

import Definitions.Def_SubSuperStoch_SubSpec_Setting
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false
open Matrix Finset SubSuperStoch.SubSpec

namespace D26Rows

lemma row_mul {n : ℕ} (F G : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    rowSum (F * G) i = ∑ k, F i k * rowSum G k := by
  change (∑ j, ∑ k, F i k * G k j) = _
  rw [sum_comm]
  simp only [rowSum, mul_sum]

lemma power_nonneg {n : ℕ} (F : Matrix (Fin n) (Fin n) ℝ)
    (hF : ∀ i j, 0 ≤ F i j) (m : ℕ) : ∀ i j, 0 ≤ (F^m) i j := by
  induction m with
  | zero => intro i j; simp only [pow_zero, Matrix.one_apply]; split_ifs <;> norm_num
  | succ m ih =>
      intro i j
      rw [pow_succ']
      change 0 ≤ ∑ k, F i k * (F^m) k j
      exact sum_nonneg (fun k _ => mul_nonneg (hF i k) (ih k j))

lemma power_row_nonneg {n : ℕ} (F : Matrix (Fin n) (Fin n) ℝ)
    (hF : ∀ i j, 0 ≤ F i j) (m : ℕ) (i : Fin n) : 0 ≤ rowSum (F^m) i :=
  sum_nonneg (fun j _ => power_nonneg F hF m i j)

lemma mul_row_le {n : ℕ} (F G : Matrix (Fin n) (Fin n) ℝ) (R : ℝ)
    (hF : ∀ i j, 0 ≤ F i j) (hG : ∀ i, rowSum G i ≤ R) (i : Fin n) :
    rowSum (F*G) i ≤ R * rowSum F i := by
  rw [row_mul]
  calc
    ∑ k, F i k * rowSum G k ≤ ∑ k, F i k * R :=
      sum_le_sum (fun k _ => mul_le_mul_of_nonneg_left (hG k) (hF i k))
    _ = _ := by simp only [rowSum]; rw [← sum_mul]; ring

lemma powers_le {n : ℕ} (F : Matrix (Fin n) (Fin n) ℝ) (R : ℝ)
    (hF : ∀ i j, 0 ≤ F i j) (hR : 0 ≤ R) (hrow : ∀ i, rowSum F i ≤ R)
    (m : ℕ) : ∀ i, rowSum (F^m) i ≤ R^m := by
  induction m with
  | zero => intro i; simp [rowSum, Matrix.one_apply]
  | succ m ih =>
      intro i
      rw [pow_succ']
      calc
        rowSum (F * F^m) i ≤ R^m * rowSum F i := mul_row_le F (F^m) (R^m) hF ih i
        _ ≤ R^m * R := mul_le_mul_of_nonneg_left (hrow i) (pow_nonneg hR m)
        _ = R^(m+1) := by rw [pow_succ]

lemma transfer {n : ℕ} (F : Matrix (Fin n) (Fin n) ℝ) (R δ a : ℝ)
    (hF : ∀ i j, 0 ≤ F i j) (hR : 0 ≤ R) (hδ : 0 ≤ δ)
    (hrow : ∀ i, rowSum F i ≤ R) (m : ℕ) (i j : Fin n)
    (hi : rowSum (F^m) i ≤ R^m - δ) (hij : a ≤ F j i) :
    rowSum (F^(m+1)) j ≤ R^(m+1) - a*δ := by
  classical
  rw [pow_succ', row_mul]
  have hterm : ∀ k, F j k * rowSum (F^m) k ≤
      F j k * (R^m - if k = i then δ else 0) := by
    intro k
    by_cases hki : k = i
    · subst k
      simpa using mul_le_mul_of_nonneg_left hi (hF j i)
    · simp only [if_neg hki, sub_zero]
      exact mul_le_mul_of_nonneg_left (powers_le F R hF hR hrow m k) (hF j k)
  calc
    ∑ k, F j k * rowSum (F^m) k ≤
        ∑ k, F j k * (R^m - if k = i then δ else 0) :=
      sum_le_sum (fun k _ => hterm k)
    _ = R^m * rowSum F j - F j i * δ := by
      simp only [mul_sub, sum_sub_distrib, mul_ite, mul_zero]
      simp [← sum_mul, rowSum, mul_comm]
    _ ≤ R^(m+1) - a*δ := by
      have h1 := mul_le_mul_of_nonneg_left (hrow j) (pow_nonneg hR m)
      have h2 := mul_le_mul_of_nonneg_right hij hδ
      rw [pow_succ]
      nlinarith only [h1,h2]

lemma retain {n : ℕ} (F : Matrix (Fin n) (Fin n) ℝ) (R α a : ℝ)
    (hF : ∀ i j, 0 ≤ F i j) (hR : 0 ≤ R) (ha : 0 ≤ a) (haR : a ≤ R)
    (hα : α ≤ R) (hrow : ∀ i, rowSum F i ≤ R)
    (m : ℕ) (i : Fin n)
    (hi : rowSum (F^(m+1)) i ≤ R^(m+1) - (R-α)*a^m) :
    rowSum (F^((m+1)+1)) i ≤ R^((m+1)+1) - (R-α)*a^(m+1) := by
  have hm := mul_row_le (F^(m+1)) F R (power_nonneg F hF (m+1)) hrow i
  have hp : 0 ≤ (R-α)*a^m := mul_nonneg (sub_nonneg.mpr hα) (pow_nonneg ha m)
  have hδ := mul_le_mul_of_nonneg_right haR hp
  have hb := mul_le_mul_of_nonneg_left hi hR
  calc
    rowSum (F^((m+1)+1)) i = rowSum (F^(m+1)*F) i := by rw [pow_succ]
    _ ≤ R * rowSum (F^(m+1)) i := hm
    _ ≤ R * (R^(m+1) - (R-α)*a^m) := hb
    _ ≤ R^((m+1)+1) - (R-α)*a^(m+1) := by
      rw [pow_succ R (m+1), pow_succ a m]
      nlinarith only [hδ]

lemma chain_bound {n : ℕ} (F : Matrix (Fin n) (Fin n) ℝ) (R α a : ℝ)
    (hF : ∀ i j, 0 ≤ F i j) (hR : 0 ≤ R) (ha : 0 ≤ a) (hα : α ≤ R)
    (hrow : ∀ i, rowSum F i ≤ R) (hmin : ∀ i j, F i j ≠ 0 → a ≤ F i j)
    (c : ℕ → Fin n) (L : ℕ) (hi : rowSum F (c 0) ≤ α) (hc : IsChain F c L) :
    rowSum (F^(L+1)) (c L) ≤ R^(L+1) - (R-α)*a^L := by
  induction L with
  | zero => simpa using hi
  | succ L ih =>
      have hcL : IsChain F c L := fun t ht => hc t (Nat.lt_trans ht (Nat.lt_succ_self L))
      have hb := ih hcL
      have he := hmin (c (L+1)) (c L) (hc L (Nat.lt_succ_self L)).1
      have ht := transfer F R ((R-α)*a^L) a hF hR
        (mul_nonneg (sub_nonneg.mpr hα) (pow_nonneg ha L)) hrow (L+1)
        (c L) (c (L+1)) hb he
      simpa [pow_succ, mul_assoc, mul_left_comm, mul_comm] using ht

lemma extend_bound {n : ℕ} (F : Matrix (Fin n) (Fin n) ℝ) (R α a : ℝ)
    (hF : ∀ i j, 0 ≤ F i j) (hR : 0 ≤ R) (ha : 0 ≤ a) (haR : a ≤ R)
    (hα : α ≤ R) (hrow : ∀ i, rowSum F i ≤ R)
    (i : Fin n) (L C : ℕ) (hLC : L ≤ C)
    (hi : rowSum (F^(L+1)) i ≤ R^(L+1) - (R-α)*a^L) :
    rowSum (F^(C+1)) i ≤ R^(C+1) - (R-α)*a^C := by
  induction C, hLC using Nat.le_induction with
  | base => exact hi
  | succ C _ ih => exact retain F R α a hF hR ha haR hα hrow C i ih

lemma scalar_data {n : ℕ} (F : Matrix (Fin n) (Fin n) ℝ)
    (hF : ∀ i j, 0 ≤ F i j) (R α a : ℝ) (hR : 1 ≤ R)
    (hrow : ∀ i, rowSum F i ≤ R)
    (hα : IsGreatest {x | ∃ s, rowSum F s < 1 ∧ x = rowSum F s} α)
    (ha : IsLeast {x | ∃ i j, 0 < F i j ∧ x = F i j} a) :
    α < 1 ∧ α ≤ R ∧ 0 < a ∧ a ≤ R ∧
      (∀ i, rowSum F i < 1 → rowSum F i ≤ α) ∧
      (∀ i j, F i j ≠ 0 → a ≤ F i j) := by
  rcases hα.1 with ⟨i, hi, rfl⟩
  rcases ha.1 with ⟨j,k,hjk,rfl⟩
  have he : F j k ≤ rowSum F j :=
    single_le_sum (fun l _ => hF j l) (mem_univ k)
  refine ⟨hi, hi.le.trans hR, hjk, he.trans (hrow j), ?_, ?_⟩
  · intro l hl
    exact hα.2 ⟨l,hl,rfl⟩
  · intro l t hlt
    exact ha.2 ⟨l,t,lt_of_le_of_ne (hF l t) (Ne.symm hlt),rfl⟩

lemma deficient_general {n : ℕ} (F : Matrix (Fin n) (Fin n) ℝ) (R α a : ℝ)
    (hF : ∀ i j, 0 ≤ F i j) (hR : 0 ≤ R) (ha : 0 ≤ a) (haR : a ≤ R)
    (hα : α ≤ R) (hrow : ∀ i, rowSum F i ≤ R)
    (i : Fin n) (hi : rowSum F i ≤ α) (C : ℕ) :
    rowSum (F^(C+1)) i ≤ R^(C+1) - (R-α)*a^C := by
  apply extend_bound F R α a hF hR ha haR hα hrow i 0 C (Nat.zero_le C)
  simpa using hi

lemma all_rows {n : ℕ} (F : Matrix (Fin n) (Fin n) ℝ) (R α a : ℝ)
    (hF : ∀ i j, 0 ≤ F i j) (hR : 0 ≤ R) (ha : 0 ≤ a) (haR : a ≤ R)
    (hα : α ≤ R) (hrow : ∀ i, rowSum F i ≤ R)
    (hmax : ∀ i, rowSum F i < 1 → rowSum F i ≤ α)
    (hmin : ∀ i j, F i j ≠ 0 → a ≤ F i j)
    (len : Fin n → ℕ) (C : ℕ)
    (hlen : ∀ k, 1 ≤ rowSum F k → len k ≤ C)
    (hchain : ∀ k, 1 ≤ rowSum F k → ∃ i, rowSum F i < 1 ∧
      ∃ c : ℕ → Fin n, c 0 = i ∧ c (len k) = k ∧ 1 ≤ len k ∧ IsChain F c (len k)) :
    ∀ k, rowSum (F^(C+1)) k ≤ R^(C+1) - (R-α)*a^C := by
  intro k
  by_cases hk : rowSum F k < 1
  · exact deficient_general F R α a hF hR ha haR hα hrow k (hmax k hk) C
  · have hge := le_of_not_gt hk
    rcases hchain k hge with ⟨i,hi,c,hc0,hcend,hL,hc⟩
    have hb := chain_bound F R α a hF hR ha hα hrow hmin c (len k)
      (by rw [hc0]; exact hmax i hi) hc
    rw [hcend] at hb
    exact extend_bound F R α a hF hR ha haR hα hrow k (len k) C (hlen k hge) hb

lemma rpow_bound_lt_one (C : ℕ) (B : ℝ) (hB : 0 ≤ B)
    (hpow : B ^ (1 / (C : ℝ)) < 1) : B < 1 := by
  have hC : 0 < C := by
    by_contra h
    have hz : C = 0 := Nat.eq_zero_of_not_pos h
    simp [hz] at hpow
  have hexp : 0 < 1 / (C : ℝ) := one_div_pos.mpr (Nat.cast_pos.mpr hC)
  exact (Real.rpow_lt_rpow_iff hB zero_le_one hexp).mp (by simpa using hpow)

end D26Rows

theorem solution {n : ℕ} (F : Matrix (Fin n) (Fin n) ℝ) (hF : IsSubStochastic F)
    (hS₁ : ∃ s, rowSum F s < 1) (hS₂ : ∃ s, rowSum F s = 1)
    (len : Fin n → ℕ)
    (hchain : ∀ k, rowSum F k = 1 → ∃ i, rowSum F i < 1 ∧
      ∃ c : ℕ → Fin n, c 0 = i ∧ c (len k) = k ∧ 1 ≤ len k ∧ IsChain F c (len k))
    (α₁ : ℝ) (hα₁ : IsGreatest {x | ∃ s, rowSum F s < 1 ∧ x = rowSum F s} α₁)
    (α₂ : ℝ) (hα₂ : IsLeast {x | ∃ i j, 0 < F i j ∧ x = F i j} α₂)
    (C : ℕ) (hC : IsGreatest {m | ∃ k, rowSum F k = 1 ∧ m = len k} C) :
    normInf (F ^ (C + 1)) ≤ 1 - (1 - α₁) * α₂ ^ C ∧ 1 - (1 - α₁) * α₂ ^ C < 1 := by
  rcases D26Rows.scalar_data F hF.1 1 α₁ α₂ le_rfl hF.2 hα₁ hα₂ with
    ⟨hαlt,hαR,ha,haR,hmax,hmin⟩
  have hlen : ∀ k, 1 ≤ rowSum F k → len k ≤ C := by
    intro k hk
    exact hC.2 ⟨k, le_antisymm (hF.2 k) hk, rfl⟩
  have hchain' : ∀ k, 1 ≤ rowSum F k → ∃ i, rowSum F i < 1 ∧
      ∃ c : ℕ → Fin n, c 0 = i ∧ c (len k) = k ∧ 1 ≤ len k ∧ IsChain F c (len k) := by
    intro k hk
    exact hchain k (le_antisymm (hF.2 k) hk)
  have hall := D26Rows.all_rows F 1 α₁ α₂ hF.1 zero_le_one ha.le haR hαR
    hF.2 hmax hmin len C hlen hchain'
  have hstrict : 1 - (1-α₁)*α₂^C < 1 := by
    have hp := mul_pos (sub_pos.mpr hαlt) (pow_pos ha C)
    linarith
  rcases hα₁.1 with ⟨i,hi,he⟩
  letI : Nonempty (Fin n) := ⟨i⟩
  refine ⟨?_,hstrict⟩
  unfold normInf
  have habs : ∀ i j, |(F^(C+1)) i j| = (F^(C+1)) i j :=
    fun i j => abs_of_nonneg (D26Rows.power_nonneg F hF.1 (C+1) i j)
  simp_rw [habs]
  apply ciSup_le
  intro k
  simpa only [rowSum,one_pow] using hall k


#print axioms solution



