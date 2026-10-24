-- Prove2me | solution 1 for SecretaryAdvice.BinaryLimit.tY_limit
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T00:32:23.582136+00:00
-- url     : https://prove2.me/submissions/d155e214-bbf5-4b84-9233-2c083e6f7625

import Mathlib
import Definitions.Def_SecretaryAdvice_BinaryLimit_Dual
import Theorems.Thm_SecretaryAdvice_BinaryLimit_dual_closed_form_late
import Theorems.Thm_SecretaryAdvice_BinaryLimit_dual_recursion
import Theorems.Thm_SecretaryAdvice_BinaryLimit_thresholds_ordered
import Theorems.Thm_SecretaryAdvice_BinaryLimit_tN_limit

open SecretaryAdvice.BinaryLimit

namespace SecBinTY

theorem stable (n : ℕ) (p pp : ℝ) (a b i : ℕ) (s : Bool) (hab : a ≤ b)
    (hi : n-a < i) : greedyStages n p pp b i s = greedyStages n p pp a i s := by
  induction b, hab using Nat.le_induction with
  | base => rfl
  | succ b hab ih =>
    simp only [greedyStages,if_neg (show i ≠ n-b by omega)]
    exact ih

theorem recurrence (n : ℕ) (p pp : ℝ) (i : ℕ) (hi : 1 ≤ i) (hin : i ≤ n) (s : Bool) :
    w n p pp i s = max 0 ((if s then p else 1-p) -
      (if s then 1-pp else pp)/(i : ℝ) *
        ∑ j ∈ Finset.Ioc i n, (w n p pp j true + w n p pp j false)) := by
  have hbase : n-(n-i)=i := by omega
  rw [w, stable n p pp (n-i+1) n i s (by omega) (by omega)]
  simp only [greedyStages,hbase,↓reduceIte]
  congr 2
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have hj' := Finset.mem_Ioc.mp hj
  congr 1 <;> symm <;> exact stable n p pp (n-i) n j _ (by omega) (by omega)

theorem nonneg_stage (n : ℕ) (p pp : ℝ) (k i : ℕ) (s : Bool) :
    0 ≤ greedyStages n p pp k i s := by
  induction k with
  | zero => simp [greedyStages]
  | succ k ih =>
    simp only [greedyStages]
    split
    · exact le_max_left _ _
    · exact ih

theorem w_nonneg (n : ℕ) (p pp : ℝ) (i : ℕ) (s : Bool) : 0 ≤ w n p pp i s :=
  nonneg_stage n p pp n i s

/-- the future sum -/
noncomputable def F (n : ℕ) (p pp : ℝ) (i : ℕ) : ℝ :=
  ∑ j ∈ Finset.Ioc i n, (w n p pp j true + w n p pp j false)

theorem F_nonneg (n : ℕ) (p pp : ℝ) (i : ℕ) : 0 ≤ F n p pp i :=
  Finset.sum_nonneg (fun _ _ => add_nonneg (w_nonneg ..) (w_nonneg ..))

theorem W_le_one (n : ℕ) (p pp : ℝ) (hpp0 : 0 ≤ pp) (hpp1 : pp ≤ 1) (hp0 : 0 ≤ p)
    (hp1 : p ≤ 1) (i : ℕ) (hi : 1 ≤ i) (hin : i ≤ n) :
    w n p pp i true + w n p pp i false ≤ 1 := by
  have hF := F_nonneg n p pp i
  unfold F at hF
  rw [recurrence n p pp i hi hin true, recurrence n p pp i hi hin false]
  simp only [if_true, Bool.false_eq_true, if_false]
  have hi' : (0:ℝ) < i := by exact_mod_cast hi
  have h1 : 0 ≤ (1 - pp) / (i:ℝ) * ∑ j ∈ Finset.Ioc i n, (w n p pp j true + w n p pp j false) :=
    mul_nonneg (div_nonneg (by linarith) hi'.le) hF
  have h2 : 0 ≤ pp / (i:ℝ) * ∑ j ∈ Finset.Ioc i n, (w n p pp j true + w n p pp j false) :=
    mul_nonneg (div_nonneg (by linarith) hi'.le) hF
  set X := ∑ j ∈ Finset.Ioc i n, (w n p pp j true + w n p pp j false)
  have hA : max 0 (p - (1 - pp) / (i:ℝ) * X) ≤ p := max_le (by linarith) (by linarith)
  have hB : max 0 (1 - p - pp / (i:ℝ) * X) ≤ 1 - p := max_le (by linarith) (by linarith)
  linarith

/-- splitting the total sum at `m` -/
theorem split_sum (n : ℕ) (p pp : ℝ) (m : ℕ) (hm : m ≤ n) :
    ∑ i ∈ Finset.Icc 1 n, (w n p pp i true + w n p pp i false) =
      ∑ i ∈ Finset.Icc 1 m, (w n p pp i true + w n p pp i false) + F n p pp m := by
  unfold F
  have e : ∀ k : ℕ, Finset.Icc 1 k = Finset.Ioc 0 k := by
    intro k; ext x; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  rw [e, e]
  exact (Finset.sum_Ioc_consecutive _ (Nat.zero_le m) hm).symm

theorem tN_props (n : ℕ) (p pp : ℝ) :
    1 ≤ tN n p pp ∧ tN n p pp ≤ n + 1 ∧
    (∀ j, 1 ≤ j → j < tN n p pp → w n p pp j false = 0) ∧
    (tN n p pp ≤ n → 0 < w n p pp (tN n p pp) false) := by
  classical
  by_cases hex : ∃ i : ℕ, 1 ≤ i ∧ i ≤ n ∧ 0 < w n p pp i false
  · have heq : tN n p pp = sInf {i : ℕ | 1 ≤ i ∧ i ≤ n ∧ 0 < w n p pp i false} := by
      unfold tN; rw [if_pos hex]
    have hmem : sInf {i : ℕ | 1 ≤ i ∧ i ≤ n ∧ 0 < w n p pp i false} ∈
        {i : ℕ | 1 ≤ i ∧ i ≤ n ∧ 0 < w n p pp i false} := Nat.sInf_mem hex
    rw [heq]
    refine ⟨hmem.1, by have := hmem.2.1; omega, ?_, fun _ => hmem.2.2⟩
    intro j hj hjT
    have hjn : j ≤ n := by have := hmem.2.1; omega
    by_contra hne
    have hpos : 0 < w n p pp j false := lt_of_le_of_ne (w_nonneg ..) (Ne.symm hne)
    have := Nat.sInf_le (show j ∈ {i : ℕ | 1 ≤ i ∧ i ≤ n ∧ 0 < w n p pp i false} from ⟨hj, hjn, hpos⟩)
    omega
  · have heq : tN n p pp = n + 1 := by
      unfold tN; rw [if_neg hex]
    rw [heq]
    refine ⟨by omega, le_refl _, ?_, fun h => by omega⟩
    intro j hj hjT
    by_contra hne
    exact hex ⟨j, hj, by omega, lt_of_le_of_ne (w_nonneg ..) (Ne.symm hne)⟩

/-- `F (T-1) = F T + W T` -/
theorem F_pred (n : ℕ) (p pp : ℝ) (T : ℕ) (hT : 1 ≤ T) (hTn : T ≤ n) :
    F n p pp (T - 1) = (w n p pp T true + w n p pp T false) + F n p pp T := by
  unfold F
  have : Finset.Ioc (T - 1) n = insert T (Finset.Ioc T n) := by
    ext x; simp only [Finset.mem_Ioc, Finset.mem_insert]; omega
  rw [this, Finset.sum_insert (by simp)]

/-- harmonic tail `∑_{k=i}^{n-1} 1/k` -/
noncomputable def H (n i : ℕ) : ℝ := ∑ k ∈ Finset.Ico i n, 1 / (k : ℝ)

theorem H_lower (n i : ℕ) (hi : 1 ≤ i) (hin : i ≤ n) :
    Real.log n - Real.log i ≤ H n i := by
  induction n, hin using Nat.le_induction with
  | base => simp [H]
  | succ m hm ih =>
    unfold H at *
    rw [Finset.sum_Ico_succ_top hm]
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hi.trans hm
    have hlog : Real.log ((m + 1 : ℕ) : ℝ) - Real.log m ≤ 1 / (m : ℝ) := by
      rw [← Real.log_div (by positivity) (by positivity)]
      have := Real.log_le_sub_one_of_pos (show 0 < ((m + 1 : ℕ) : ℝ) / m by positivity)
      have h2 : ((m + 1 : ℕ) : ℝ) / m - 1 = 1 / m := by
        push_cast; field_simp; ring
      linarith
    linarith

theorem H_upper (n i : ℕ) (hi : 2 ≤ i) (hin : i ≤ n) :
    H n i ≤ Real.log ((n : ℝ) - 1) - Real.log ((i : ℝ) - 1) := by
  induction n, hin using Nat.le_induction with
  | base => simp [H]
  | succ m hm ih =>
    unfold H at *
    rw [Finset.sum_Ico_succ_top hm]
    have hm1 : (2 : ℝ) ≤ m := by exact_mod_cast hi.trans hm
    have hlog : 1 / (m : ℝ) ≤ Real.log ((m + 1 : ℕ) - 1 : ℝ) - Real.log ((m : ℝ) - 1) := by
      push_cast
      rw [add_sub_cancel_right, ← Real.log_div (by positivity) (by linarith)]
      have := Real.log_le_sub_one_of_pos (show 0 < ((m : ℝ) - 1) / m by
        apply div_pos <;> linarith)
      rw [Real.log_div (by linarith) (by positivity)] at this
      rw [Real.log_div (by positivity) (by linarith)]
      have h2 : ((m : ℝ) - 1) / m - 1 = -(1 / m) := by
        field_simp; ring
      linarith
    linarith

/-- Two-sided characterisation of `t_N` through the harmonic tail. -/
theorem tN_char (n : ℕ) (p pp : ℝ) (hn : 1 ≤ n) (hp0 : (1 / 2 : ℝ) ≤ p) (hp1 : p ≤ 1)
    (hpp0 : (1 / 2 : ℝ) ≤ pp) (hpp1 : pp ≤ 1) (hT : tN n p pp ≤ n) :
    pp * H n (tN n p pp) < 1 - p ∧
    (2 ≤ tN n p pp → 1 - p ≤ pp * H n (tN n p pp - 1) ∧
      F n p pp (tN n p pp - 1) = ((tN n p pp : ℝ) - 1) * H n (tN n p pp - 1)) := by
  obtain ⟨hT1, -, hzeroN, hpos⟩ := tN_props n p pp
  set T := tN n p pp with hTdef
  have hcl := dual_closed_form_late n p pp hn hp0 hp1 hpp0 hpp1 T le_rfl hT
  have hsY : ∑ j ∈ Finset.Ico T n, (1 - pp) / (j : ℝ) = (1 - pp) * H n T := by
    unfold H; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring
  have hsN : ∑ j ∈ Finset.Ico T n, pp / (j : ℝ) = pp * H n T := by
    unfold H; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring
  rw [hsY] at hcl; rw [hsN] at hcl
  have hwpos := hpos hT
  have ha : pp * H n T < 1 - p := by rw [hcl.2] at hwpos; linarith
  refine ⟨ha, fun hT2 => ?_⟩
  -- the value of `F T` from the recurrence
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT1
  have hrec := recurrence n p pp T hT1 hT false
  simp only [Bool.false_eq_true, if_false] at hrec
  change w n p pp T false = max 0 (1 - p - pp / (T : ℝ) * F n p pp T) at hrec
  have hFT : F n p pp T = T * H n T := by
    have h1 : w n p pp T false = 1 - p - pp / (T : ℝ) * F n p pp T := by
      rw [hrec]; apply max_eq_right
      have := hrec ▸ hwpos
      rcases lt_max_iff.mp this with h | h
      · exact absurd h (lt_irrefl 0)
      · exact h.le
    rw [hcl.2] at h1
    have hpp : 0 < pp := by linarith
    have : pp / (T : ℝ) * F n p pp T = pp * H n T := by linarith
    field_simp at this
    linarith
  have hFT1 : F n p pp (T - 1) = ((T : ℝ) - 1) * H n (T - 1) := by
    rw [F_pred n p pp T hT1 hT, hcl.1, hcl.2, hFT]
    unfold H
    rw [Finset.sum_eq_sum_Ico_succ_bot (show T - 1 < n by omega), show T - 1 + 1 = T by omega,
      Nat.cast_sub (by omega)]
    have : ((T : ℝ) - (1 : ℕ)) ≠ 0 := by
      have : (2 : ℝ) ≤ T := by exact_mod_cast hT2
      push_cast; linarith
    field_simp
    push_cast
    ring
  have hw0 := hzeroN (T - 1) (by omega) (by omega)
  rw [recurrence n p pp (T - 1) (by omega) (by omega) false] at hw0
  simp only [Bool.false_eq_true, if_false] at hw0
  have hle := max_eq_left_iff.mp hw0
  change 1 - p - pp / ((T - 1 : ℕ) : ℝ) * F n p pp (T - 1) ≤ 0 at hle
  rw [hFT1, Nat.cast_sub (by omega)] at hle
  have hT' : ((T : ℝ) - (1 : ℕ)) ≠ 0 := by
    have : (2 : ℝ) ≤ T := by exact_mod_cast hT2
    push_cast; linarith
  have : pp / ((T : ℝ) - (1 : ℕ)) * (((T : ℝ) - 1) * H n (T - 1)) = pp * H n (T - 1) := by
    push_cast at hT' ⊢; field_simp
  rw [this] at hle
  exact ⟨by linarith, hFT1⟩

/-- If `p = 1` the `N` threshold is `n + 1`. -/
theorem tN_p_one (n : ℕ) (pp : ℝ) (hpp0 : 0 ≤ pp) : tN n 1 pp = n + 1 := by
  obtain ⟨-, hTn, -, hpos⟩ := tN_props n 1 pp
  by_contra hne
  have hT : tN n 1 pp ≤ n := by omega
  have h := hpos hT
  rw [recurrence n 1 pp _ (tN_props n 1 pp).1 hT false] at h
  simp only [Bool.false_eq_true, if_false, sub_self, zero_sub] at h
  have hF := F_nonneg n 1 pp (tN n 1 pp)
  unfold F at hF
  have : 0 ≤ pp / ((tN n 1 pp : ℕ) : ℝ) *
      ∑ j ∈ Finset.Ioc (tN n 1 pp) n, (w n 1 pp j true + w n 1 pp j false) :=
    mul_nonneg (div_nonneg hpp0 (Nat.cast_nonneg _)) hF
  rw [max_eq_left (by linarith)] at h
  exact lt_irrefl _ h

theorem tY_props (n : ℕ) (p pp : ℝ) :
    1 ≤ tY n p pp ∧ tY n p pp ≤ n + 1 ∧
    (∀ j, 1 ≤ j → j < tY n p pp → w n p pp j true = 0) ∧
    (tY n p pp ≤ n → 0 < w n p pp (tY n p pp) true) := by
  classical
  by_cases hex : ∃ i : ℕ, 1 ≤ i ∧ i ≤ n ∧ 0 < w n p pp i true
  · have heq : tY n p pp = sInf {i : ℕ | 1 ≤ i ∧ i ≤ n ∧ 0 < w n p pp i true} := by
      unfold tY; rw [if_pos hex]
    have hmem : sInf {i : ℕ | 1 ≤ i ∧ i ≤ n ∧ 0 < w n p pp i true} ∈
        {i : ℕ | 1 ≤ i ∧ i ≤ n ∧ 0 < w n p pp i true} := Nat.sInf_mem hex
    rw [heq]
    refine ⟨hmem.1, by have := hmem.2.1; omega, ?_, fun _ => hmem.2.2⟩
    intro j hj hjT
    have hjn : j ≤ n := by have := hmem.2.1; omega
    by_contra hne
    have hpos : 0 < w n p pp j true := lt_of_le_of_ne (w_nonneg ..) (Ne.symm hne)
    have := Nat.sInf_le (show j ∈ {i : ℕ | 1 ≤ i ∧ i ≤ n ∧ 0 < w n p pp i true} from ⟨hj, hjn, hpos⟩)
    omega
  · have heq : tY n p pp = n + 1 := by
      unfold tY; rw [if_neg hex]
    rw [heq]
    refine ⟨by omega, le_refl _, ?_, fun h => by omega⟩
    intro j hj hjT
    by_contra hne
    exact hex ⟨j, hj, by omega, lt_of_le_of_ne (w_nonneg ..) (Ne.symm hne)⟩

theorem coord_mono_Y (n : ℕ) (p pp : ℝ) (hpp1 : pp ≤ 1)
    (i j : ℕ) (hi : 1 ≤ i) (hij : i ≤ j) (hjn : j ≤ n) :
    w n p pp i true ≤ w n p pp j true := by
  rw [recurrence n p pp i hi (hij.trans hjn) true, recurrence n p pp j (hi.trans hij) hjn true]
  simp only [if_true]
  apply max_le_max_left
  have ha : 0 ≤ 1 - pp := by linarith
  have hFj : 0 ≤ ∑ k ∈ Finset.Ioc j n, (w n p pp k true + w n p pp k false) :=
    Finset.sum_nonneg (fun k _ => add_nonneg (w_nonneg ..) (w_nonneg ..))
  have hF : (∑ k ∈ Finset.Ioc j n, (w n p pp k true + w n p pp k false)) ≤
      ∑ k ∈ Finset.Ioc i n, (w n p pp k true + w n p pp k false) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro k hk
      simp only [Finset.mem_Ioc] at *
      omega
    · intro k _ _
      exact add_nonneg (w_nonneg ..) (w_nonneg ..)
  have hden : (1 - pp)/(j : ℝ) ≤ (1 - pp)/(i : ℝ) :=
    div_le_div_of_nonneg_left ha (by exact_mod_cast hi) (by exact_mod_cast hij)
  exact sub_le_sub_left (mul_le_mul hden hF hFj (div_nonneg ha (Nat.cast_nonneg i))) _

theorem tN_le (n : ℕ) (p pp : ℝ) (hn : 1 ≤ n) (hp1 : p < 1) : tN n p pp ≤ n := by
  by_contra hne
  have hzero := (tN_props n p pp).2.2.1 n hn (by omega)
  rw [recurrence n p pp n hn le_rfl false] at hzero
  simp only [Bool.false_eq_true, if_false] at hzero
  have : F n p pp n = 0 := by unfold F; simp
  unfold F at this
  rw [this, mul_zero, sub_zero] at hzero
  have := max_eq_left_iff.mp hzero
  linarith

/-- The anchor of the backward recursion at `m = t_N - 1`. -/
theorem anchor (n : ℕ) (p pp : ℝ) (hn : 1 ≤ n) (hp0 : (1 / 2 : ℝ) ≤ p) (hp1 : p ≤ 1)
    (hpp0 : (1 / 2 : ℝ) ≤ pp) (hpp1 : pp ≤ 1) (hT2 : 2 ≤ tN n p pp) :
    F n p pp (tN n p pp - 1) = ((tN n p pp : ℝ) - 1) * H n (tN n p pp - 1) ∧
    (1 - p) / pp ≤ H n (tN n p pp - 1) ∧
    H n (tN n p pp - 1) ≤ (1 - p) / pp + 1 / ((tN n p pp : ℝ) - 1) := by
  have hpp : 0 < pp := by linarith
  rcases hp1.lt_or_eq with hp1' | hp1'
  · have hT := tN_le n p pp hn hp1'
    obtain ⟨ha, hb⟩ := tN_char n p pp hn hp0 hp1 hpp0 hpp1 hT
    obtain ⟨hb1, hb2⟩ := hb hT2
    refine ⟨hb2, by rw [div_le_iff₀ hpp]; linarith, ?_⟩
    have hsplit : H n (tN n p pp - 1) = 1 / ((tN n p pp : ℝ) - 1) + H n (tN n p pp) := by
      unfold H
      rw [Finset.sum_eq_sum_Ico_succ_bot (show tN n p pp - 1 < n by omega),
        show tN n p pp - 1 + 1 = tN n p pp by omega, Nat.cast_sub (by omega)]
      push_cast; ring
    have : H n (tN n p pp) ≤ (1 - p) / pp := by rw [le_div_iff₀ hpp]; linarith
    linarith
  · subst hp1'
    have hT := tN_p_one n pp hpp.le
    rw [hT, show n + 1 - 1 = n by omega]
    have hH : H n n = 0 := by unfold H; simp
    have hF : F n 1 pp n = 0 := by unfold F; simp
    rw [hH, hF]
    have h1 : (1:ℝ) ≤ n := by exact_mod_cast hn
    have : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) - 1 := by push_cast; linarith
    refine ⟨by ring, by simp, ?_⟩
    simp only [sub_self, zero_div, zero_add]
    positivity

/-- `log ∏_{j=k}^{m-1} (1 + pp/j)` -/
noncomputable def LP (pp : ℝ) (k m : ℕ) : ℝ := ∑ j ∈ Finset.Ico k m, Real.log (1 + pp / (j : ℝ))

theorem LP_step (pp : ℝ) (hpp : 0 ≤ pp) (k m : ℕ) (hk : 1 ≤ k) (hkm : k < m) :
    Real.exp (LP pp k m) = (1 + pp / (k : ℝ)) * Real.exp (LP pp (k + 1) m) := by
  unfold LP
  rw [Finset.sum_eq_sum_Ico_succ_bot hkm, Real.exp_add, Real.exp_log]
  have : (0 : ℝ) < k := by exact_mod_cast hk
  positivity

theorem LP_upper (pp : ℝ) (hpp : 0 ≤ pp) (k m : ℕ) (hk : 2 ≤ k) (hkm : k ≤ m) :
    LP pp k m ≤ pp * (Real.log ((m : ℝ) - 1) - Real.log ((k : ℝ) - 1)) := by
  induction m, hkm using Nat.le_induction with
  | base => simp [LP]
  | succ m hm ih =>
    unfold LP at *
    rw [Finset.sum_Ico_succ_top hm]
    have hm1 : (2 : ℝ) ≤ m := by exact_mod_cast hk.trans hm
    have h1 : Real.log (1 + pp / (m : ℝ)) ≤ pp / m := by
      have := Real.log_le_sub_one_of_pos (show 0 < 1 + pp / (m : ℝ) by positivity)
      linarith
    have h2 : 1 / (m : ℝ) ≤ Real.log ((m + 1 : ℕ) - 1 : ℝ) - Real.log ((m : ℝ) - 1) := by
      push_cast
      rw [add_sub_cancel_right]
      have := Real.log_le_sub_one_of_pos (show 0 < ((m : ℝ) - 1) / m by
        apply div_pos <;> linarith)
      rw [Real.log_div (by linarith) (by positivity)] at this
      have h3 : ((m : ℝ) - 1) / m - 1 = -(1 / m) := by
        field_simp; ring
      linarith
    have h3 : pp / (m : ℝ) = pp * (1 / m) := by ring
    nlinarith

theorem LP_lower (pp : ℝ) (hpp : 0 ≤ pp) (hpp1 : pp ≤ 1) (k m : ℕ) (hk : 1 ≤ k) (hkm : k ≤ m) :
    pp * (Real.log ((m : ℝ) + 1) - Real.log ((k : ℝ) + 1)) ≤ LP pp k m := by
  induction m, hkm using Nat.le_induction with
  | base => simp [LP]
  | succ m hm ih =>
    unfold LP at *
    rw [Finset.sum_Ico_succ_top hm]
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hk.trans hm
    -- log(1+x) ≥ x/(1+x) ≥ pp/(m+1)
    have h1 : pp / ((m : ℝ) + 1) ≤ Real.log (1 + pp / (m : ℝ)) := by
      have hpos : 0 < 1 + pp / (m : ℝ) := by positivity
      have := Real.log_le_sub_one_of_pos (inv_pos.mpr hpos)
      rw [Real.log_inv] at this
      have h4 : (1 + pp / (m : ℝ))⁻¹ - 1 = -(pp / ((m : ℝ) + pp)) := by
        field_simp; ring
      have h5 : pp / ((m : ℝ) + 1) ≤ pp / ((m : ℝ) + pp) :=
        div_le_div_of_nonneg_left hpp (by linarith) (by linarith)
      linarith
    have h2 : Real.log (((m + 1 : ℕ) : ℝ) + 1) - Real.log ((m : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) := by
      push_cast
      rw [← Real.log_div (by positivity) (by positivity)]
      have := Real.log_le_sub_one_of_pos (show 0 < ((m : ℝ) + 1 + 1) / ((m : ℝ) + 1) by positivity)
      have h3 : ((m : ℝ) + 1 + 1) / ((m : ℝ) + 1) - 1 = 1 / ((m : ℝ) + 1) := by
        field_simp; ring
      linarith
    have h3 : pp / ((m : ℝ) + 1) = pp * (1 / ((m : ℝ) + 1)) := by ring
    nlinarith

/-- closed form of `w^Y` between `t_Y` and `m = t_N - 1` -/
theorem wY_closed (n : ℕ) (p pp : ℝ) (hn : 1 ≤ n) (hp0 : (1 / 2 : ℝ) ≤ p) (hp1 : p ≤ 1)
    (hpp0 : (1 / 2 : ℝ) ≤ pp) (hpp1 : pp ≤ 1) (hT2 : 2 ≤ tN n p pp)
    (k : ℕ) (hk : tY n p pp ≤ k) (hkm : k ≤ tN n p pp - 1) :
    w n p pp k true = p / pp - Real.exp (LP pp k (tN n p pp - 1)) *
      (p / pp - (p - (1 - pp) * H n (tN n p pp - 1))) := by
  obtain ⟨hY1, -, -, hYpos⟩ := tY_props n p pp
  obtain ⟨-, hNn, -, -⟩ := tN_props n p pp
  set m := tN n p pp - 1 with hm
  have hmn : m ≤ n := by omega
  have hm1 : 1 ≤ m := by omega
  have hpp : 0 < pp := by linarith
  -- base
  have hbase : w n p pp m true = p - (1 - pp) * H n m := by
    have hpos : 0 < w n p pp m true :=
      (hYpos (by omega)).trans_le (coord_mono_Y n p pp hpp1 _ m hY1 (by omega) hmn)
    have hrec := recurrence n p pp m hm1 hmn true
    simp only [if_true] at hrec
    change w n p pp m true = max 0 (p - (1 - pp) / (m : ℝ) * F n p pp m) at hrec
    have hF := (anchor n p pp hn hp0 hp1 hpp0 hpp1 hT2).1
    rw [← hm] at hF
    have hmR : ((tN n p pp : ℝ) - 1) = (m : ℝ) := by
      rw [hm, Nat.cast_sub (by omega)]; simp
    rw [hmR] at hF
    rw [hF] at hrec
    have hmpos : (0 : ℝ) < m := by exact_mod_cast hm1
    have : (1 - pp) / (m : ℝ) * ((m : ℝ) * H n m) = (1 - pp) * H n m := by
      field_simp
    rw [this] at hrec
    rw [hrec] at hpos ⊢
    apply max_eq_right
    rcases lt_max_iff.mp hpos with h | h
    · exact absurd h (lt_irrefl 0)
    · exact h.le
  -- downward induction
  have key : ∀ d : ℕ, ∀ k, k + d = m → tY n p pp ≤ k →
      w n p pp k true = p / pp - Real.exp (LP pp k m) * (p / pp - (p - (1 - pp) * H n m)) := by
    intro d
    induction d with
    | zero =>
      intro k hkd _
      simp only [add_zero] at hkd
      subst hkd
      rw [hbase]
      simp only [LP, Finset.Ico_self, Finset.sum_empty, Real.exp_zero]
      ring
    | succ d ih =>
      intro k hkd hk
      have hk1 : 1 ≤ k := hY1.trans hk
      have hrec := dual_recursion n p pp hn hp0 hp1 hpp0 hpp1 k hk1 hk (by omega)
      rw [hrec, ih (k + 1) (by omega) (by omega), LP_step pp hpp.le k m hk1 (by omega)]
      have hkpos : (0 : ℝ) < k := by exact_mod_cast hk1
      field_simp
      ring
  exact key (m - k) k (by omega) hk

/-- The two inequalities that pin down `t_Y`. -/
theorem tY_char (n : ℕ) (p pp : ℝ) (hn : 1 ≤ n) (hp0 : (1 / 2 : ℝ) ≤ p) (hp1 : p ≤ 1)
    (hpp0 : (1 / 2 : ℝ) ≤ pp) (hpp1 : pp < 1) (hT2 : 2 ≤ tN n p pp) :
    (tY n p pp ≤ tN n p pp - 1 →
      Real.exp (LP pp (tY n p pp) (tN n p pp - 1)) *
        (p / pp - (p - (1 - pp) * H n (tN n p pp - 1))) < p / pp) ∧
    (2 ≤ tY n p pp →
      p / pp ≤ Real.exp (LP pp (tY n p pp - 1) (tN n p pp - 1)) *
        (p / pp - (p - (1 - pp) * H n (tN n p pp - 1)))) := by
  obtain ⟨hY1, hYn, hYzero, hYpos⟩ := tY_props n p pp
  obtain ⟨-, hNn, hNzero, -⟩ := tN_props n p pp
  have hord := thresholds_ordered n p pp hn hp0 hp1 hpp0 hpp1.le
  set m := tN n p pp - 1 with hm
  set c := p / pp - (p - (1 - pp) * H n m) with hc
  have hpp : 0 < pp := by linarith
  constructor
  · intro hYm
    have hpos := hYpos (by omega)
    rw [wY_closed n p pp hn hp0 hp1 hpp0 hpp1.le hT2 _ le_rfl hYm] at hpos
    linarith
  · intro hY2
    set T := tY n p pp with hTdef
    rcases Nat.lt_or_ge m T with hmT | hmT
    · -- `T = t_N`, so `k = m`
      have hTm : T - 1 = m := by omega
      rw [hTm, show LP pp m m = 0 by simp [LP], Real.exp_zero, one_mul]
      have hw := hYzero m (by omega) (by omega)
      rw [recurrence n p pp m (by omega) (by omega) true] at hw
      simp only [if_true] at hw
      have hle := max_eq_left_iff.mp hw
      change p - (1 - pp) / (m : ℝ) * F n p pp m ≤ 0 at hle
      have hF := (anchor n p pp hn hp0 hp1 hpp0 hpp1.le hT2).1
      rw [← hm] at hF
      have hmR : ((tN n p pp : ℝ) - 1) = (m : ℝ) := by
        rw [hm, Nat.cast_sub (by omega)]; simp
      rw [hmR] at hF
      rw [hF] at hle
      have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 1 ≤ m by omega)
      have : (1 - pp) / (m : ℝ) * ((m : ℝ) * H n m) = (1 - pp) * H n m := by
        field_simp
      rw [this] at hle
      rw [hc]; linarith
    · -- `T ≤ m`
      set k := T - 1 with hk
      have hk1 : 1 ≤ k := by omega
      rw [LP_step pp hpp.le k m hk1 (by omega), show k + 1 = T by omega]
      have hwT := wY_closed n p pp hn hp0 hp1 hpp0 hpp1.le hT2 T le_rfl hmT
      rw [← hm, ← hc] at hwT
      have hE : Real.exp (LP pp T m) * c = p / pp - w n p pp T true := by linarith
      rw [mul_assoc, hE]
      -- the vanishing of `w^Y_{T-1}`
      have hw := hYzero k hk1 (by omega)
      rw [recurrence n p pp k hk1 (by omega) true] at hw
      simp only [if_true] at hw
      have hle := max_eq_left_iff.mp hw
      change p - (1 - pp) / (k : ℝ) * F n p pp k ≤ 0 at hle
      have hFk : F n p pp k = (w n p pp T true + w n p pp T false) + F n p pp T := by
        rw [hk]; exact F_pred n p pp T hY1 (by omega)
      have hNT : w n p pp T false = 0 := hNzero T hY1 (by omega)
      rw [hFk, hNT, add_zero] at hle
      -- `F_T` from the positive coordinate at `T`
      have hpos := hYpos (by omega)
      have hrecT := recurrence n p pp T hY1 (by omega) true
      simp only [if_true] at hrecT
      change w n p pp T true = max 0 (p - (1 - pp) / (T : ℝ) * F n p pp T) at hrecT
      have hwT' : w n p pp T true = p - (1 - pp) / (T : ℝ) * F n p pp T := by
        rw [hrecT]; apply max_eq_right
        rw [hrecT] at hpos
        rcases lt_max_iff.mp hpos with h | h
        · exact absurd h (lt_irrefl 0)
        · exact h.le
      have hTpos : (0 : ℝ) < T := by exact_mod_cast hY1
      have hkpos : (0 : ℝ) < k := by exact_mod_cast hk1
      have hTk : (T : ℝ) = k + 1 := by
        rw [hk, Nat.cast_sub (by omega)]; simp
      have hcpp : 0 < 1 - pp := by linarith
      have hFT : F n p pp T = (p - w n p pp T true) * T / (1 - pp) := by
        rw [hwT']; field_simp; ring
      rw [hFT, hTk] at hle
      set x := w n p pp T true
      -- hle : p - (1-pp)/k * (x + (p - x)(k+1)/(1-pp)) ≤ 0
      have h1 : (1 - pp) / (k : ℝ) * (x + (p - x) * ((k : ℝ) + 1) / (1 - pp)) =
          ((1 - pp) * x + (p - x) * ((k : ℝ) + 1)) / k := by
        field_simp
      rw [h1, sub_nonpos, le_div_iff₀ hkpos] at hle
      rw [div_le_iff₀ hpp]
      have h2 : (1 + pp / (k : ℝ)) * (p / pp - x) * pp = (k + pp) * (p - pp * x) / k := by
        field_simp
      rw [h2, le_div_iff₀ hkpos]
      nlinarith

/-- the constant `c_n = p/p' - v_m` -/
noncomputable def cc (n : ℕ) (p pp : ℝ) : ℝ := p / pp - (p - (1 - pp) * H n (tN n p pp - 1))

theorem H_nonneg (n i : ℕ) : 0 ≤ H n i :=
  Finset.sum_nonneg (fun _ _ => by positivity)

theorem cc_pos (n : ℕ) (p pp : ℝ) (hp0 : (1 / 2 : ℝ) ≤ p) (hpp0 : (1 / 2 : ℝ) ≤ pp)
    (hpp1 : pp < 1) : 0 < cc n p pp := by
  unfold cc
  have hpp : 0 < pp := by linarith
  have h1 : 0 ≤ (1 - pp) * H n (tN n p pp - 1) := mul_nonneg (by linarith) (H_nonneg ..)
  have h2 : p < p / pp := by rw [lt_div_iff₀ hpp]; nlinarith
  linarith

/-- integer bounds on `t_Y` -/
theorem tY_bounds (n : ℕ) (p pp : ℝ) (hn : 1 ≤ n) (hp0 : (1 / 2 : ℝ) ≤ p) (hp1 : p ≤ 1)
    (hpp0 : (1 / 2 : ℝ) ≤ pp) (hpp1 : pp < 1) (hT3 : 3 ≤ tN n p pp) :
    (tY n p pp : ℝ) ≤ ((tN n p pp : ℝ) - 2) *
        Real.exp (-(Real.log (p / pp) - Real.log (cc n p pp)) / pp) + 2 ∧
    min (tN n p pp : ℝ) ((tN n p pp : ℝ) *
        Real.exp (-(Real.log (p / pp) - Real.log (cc n p pp)) / pp) - 1) ≤ tY n p pp := by
  have hpp : 0 < pp := by linarith
  have hp : 0 < p := by linarith
  have hc := cc_pos n p pp hp0 hpp0 hpp1
  obtain ⟨hA, hB⟩ := tY_char n p pp hn hp0 hp1 hpp0 hpp1 (by omega)
  change _ → Real.exp _ * cc n p pp < _ at hA
  change _ → _ ≤ Real.exp _ * cc n p pp at hB
  obtain ⟨hY1, -, -, -⟩ := tY_props n p pp
  have hord := thresholds_ordered n p pp hn hp0 hp1 hpp0 hpp1.le
  set E := Real.exp (-(Real.log (p / pp) - Real.log (cc n p pp)) / pp) with hE
  have hEpos : 0 < E := Real.exp_pos _
  set T := tY n p pp with hTdef
  set N := tN n p pp with hNdef
  have hN3 : (3 : ℝ) ≤ N := by exact_mod_cast hT3
  constructor
  · rcases Nat.lt_or_ge T 3 with h3 | h3
    · have : (T : ℝ) ≤ 2 := by exact_mod_cast (show T ≤ 2 by omega)
      have : 0 ≤ ((N : ℝ) - 2) * E := mul_nonneg (by linarith) hEpos.le
      linarith
    · have hb := hB (by omega)
      have hu := LP_upper pp hpp.le (T - 1) (N - 1) (by omega) (by omega)
      have hcast1 : ((N - 1 : ℕ) : ℝ) - 1 = (N : ℝ) - 2 := by
        rw [Nat.cast_sub (by omega)]; push_cast; ring
      have hcast2 : ((T - 1 : ℕ) : ℝ) - 1 = (T : ℝ) - 2 := by
        rw [Nat.cast_sub (by omega)]; push_cast; ring
      rw [hcast1, hcast2] at hu
      have hT2 : (0 : ℝ) < (T : ℝ) - 2 := by
        have : (3 : ℝ) ≤ T := by exact_mod_cast h3
        linarith
      have hN2 : (0 : ℝ) < (N : ℝ) - 2 := by linarith
      -- take logs in hb
      have hlog : Real.log (p / pp) ≤ LP pp (T - 1) (N - 1) + Real.log (cc n p pp) := by
        have := Real.log_le_log (by positivity) hb
        rwa [Real.log_mul (Real.exp_pos _).ne' hc.ne', Real.log_exp] at this
      have hlog2 : Real.log ((T : ℝ) - 2) ≤
          Real.log ((N : ℝ) - 2) + (-(Real.log (p / pp) - Real.log (cc n p pp)) / pp) := by
        rw [div_eq_mul_inv]
        have : Real.log (p / pp) - Real.log (cc n p pp) ≤
            pp * (Real.log ((N : ℝ) - 2) - Real.log ((T : ℝ) - 2)) := by linarith
        have h' : (Real.log (p / pp) - Real.log (cc n p pp)) * pp⁻¹ ≤
            Real.log ((N : ℝ) - 2) - Real.log ((T : ℝ) - 2) := by
          rw [← div_eq_mul_inv, div_le_iff₀ hpp]; linarith
        linarith
      have := Real.exp_le_exp.mpr hlog2
      rw [Real.exp_add, Real.exp_log hT2, Real.exp_log hN2, ← hE] at this
      linarith
  · rcases Nat.lt_or_ge (N - 1) T with h | h
    · have : (N : ℝ) ≤ T := by exact_mod_cast (show N ≤ T by omega)
      exact (min_le_left _ _).trans this
    · apply (min_le_right _ _).trans
      have ha := hA h
      have hl := LP_lower pp hpp.le hpp1.le T (N - 1) hY1 h
      have hcast1 : ((N - 1 : ℕ) : ℝ) + 1 = (N : ℝ) := by
        rw [Nat.cast_sub (by omega)]; push_cast; ring
      rw [hcast1] at hl
      have hTpos : (0 : ℝ) < (T : ℝ) + 1 := by positivity
      have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
      have hlog : LP pp T (N - 1) + Real.log (cc n p pp) < Real.log (p / pp) := by
        have := Real.log_lt_log (by positivity) ha
        rwa [Real.log_mul (Real.exp_pos _).ne' hc.ne', Real.log_exp] at this
      have hlog2 : Real.log (N : ℝ) + (-(Real.log (p / pp) - Real.log (cc n p pp)) / pp) <
          Real.log ((T : ℝ) + 1) := by
        have : pp * (Real.log (N : ℝ) - Real.log ((T : ℝ) + 1)) <
            Real.log (p / pp) - Real.log (cc n p pp) := by linarith
        have h' : Real.log (N : ℝ) - Real.log ((T : ℝ) + 1) <
            (Real.log (p / pp) - Real.log (cc n p pp)) / pp := by
          rw [lt_div_iff₀ hpp]; linarith
        rw [neg_div]
        linarith
      have := Real.exp_lt_exp.mpr hlog2
      rw [Real.exp_add, Real.exp_log hTpos, Real.exp_log hNpos, ← hE] at this
      linarith

theorem tY_pp_one (n : ℕ) (p : ℝ) (hn : 1 ≤ n) (hp0 : (1 / 2 : ℝ) ≤ p) : tY n p 1 = 1 := by
  obtain ⟨hY1, -, hz, -⟩ := tY_props n p 1
  by_contra hne
  have h := hz 1 le_rfl (by omega)
  rw [recurrence n p 1 1 le_rfl hn true] at h
  simp only [if_true, sub_self, zero_div, zero_mul, sub_zero] at h
  have := max_eq_left_iff.mp h
  linarith

end SecBinTY

open SecBinTY in
theorem solution (p pp : ℝ) (hp0 : (1 / 2 : ℝ) ≤ p) (hp1 : p ≤ 1) (hpp0 : (1 / 2 : ℝ) ≤ pp) (hpp1 : pp ≤ 1) :
    Filter.Tendsto (fun n : ℕ => (tY n p pp : ℝ) / (n : ℝ)) Filter.atTop
      (nhds (((1 - pp) / p) ^ (1 / pp) * Real.exp (p / pp - 1 / pp))) := by
  have hinv : Filter.Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ)) Filter.atTop (nhds 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have hp : 0 < p := by linarith
  have hpp : 0 < pp := by linarith
  rcases hpp1.lt_or_eq with hpp1 | hpp1
  swap
  · subst hpp1
    have : ((1 - 1) / p) ^ (1 / (1 : ℝ)) * Real.exp (p / 1 - 1 / 1) = 0 := by simp
    rw [this]
    apply hinv.congr'
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    rw [tY_pp_one n p hn hp0]; simp
  set LN := Real.exp (p / pp - 1 / pp) with hLN
  have hLNpos : 0 < LN := Real.exp_pos _
  have hN := tN_limit p pp hp0 hp1 hpp0 hpp1.le
  -- `t_N → ∞`
  have hNinf : Filter.Tendsto (fun n : ℕ => (tN n p pp : ℝ)) Filter.atTop Filter.atTop := by
    have := hN.pos_mul_atTop hLNpos tendsto_natCast_atTop_atTop
    apply this.congr'
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    have h1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have : (n : ℝ) ≠ 0 := by linarith
    field_simp
  have hev3 : ∀ᶠ n : ℕ in Filter.atTop, 3 ≤ tN n p pp := by
    filter_upwards [hNinf.eventually_ge_atTop 3] with n hn
    exact_mod_cast hn
  -- `H(t_N - 1) → α`
  set α := (1 - p) / pp with hα
  have hinvN : Filter.Tendsto (fun n : ℕ => 1 / ((tN n p pp : ℝ) - 1)) Filter.atTop (nhds 0) := by
    have := (Filter.tendsto_atTop_add_const_right _ (-1) hNinf).inv_tendsto_atTop
    refine this.congr (fun n => ?_)
    simp [sub_eq_add_neg, one_div]
  have hH : Filter.Tendsto (fun n : ℕ => H n (tN n p pp - 1)) Filter.atTop (nhds α) := by
    have hhi : Filter.Tendsto (fun n : ℕ => α + 1 / ((tN n p pp : ℝ) - 1)) Filter.atTop
        (nhds α) := by simpa using hinvN.const_add α
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hhi
    · filter_upwards [Filter.eventually_ge_atTop 1, hev3] with n hn h3
      exact (anchor n p pp hn hp0 hp1 hpp0 hpp1.le (by omega)).2.1
    · filter_upwards [Filter.eventually_ge_atTop 1, hev3] with n hn h3
      exact (anchor n p pp hn hp0 hp1 hpp0 hpp1.le (by omega)).2.2
  set cI := (1 - pp) / pp with hcinf
  have hcinfpos : 0 < cI := div_pos (by linarith) hpp
  have hc : Filter.Tendsto (fun n : ℕ => cc n p pp) Filter.atTop (nhds cI) := by
    have : cI = p / pp - (p - (1 - pp) * α) := by
      rw [hcinf, hα]; field_simp; ring
    rw [this]
    exact tendsto_const_nhds.sub (tendsto_const_nhds.sub (hH.const_mul _))
  set Λ := Real.log (p / pp) - Real.log cI
  have hE : Filter.Tendsto (fun n : ℕ =>
      Real.exp (-(Real.log (p / pp) - Real.log (cc n p pp)) / pp)) Filter.atTop
      (nhds (Real.exp (-Λ / pp))) := by
    apply (Real.continuous_exp.tendsto _).comp
    exact ((tendsto_const_nhds.sub (hc.log hcinfpos.ne')).neg).div_const pp
  set E := Real.exp (-Λ / pp)
  have hEle : E ≤ 1 := by
    rw [Real.exp_le_one_iff, neg_div, neg_nonpos]
    apply div_nonneg _ hpp.le
    rw [sub_nonneg]
    apply Real.log_le_log hcinfpos
    rw [hcinf]; apply div_le_div_of_nonneg_right _ hpp.le; linarith
  have htarget : ((1 - pp) / p) ^ (1 / pp) * LN = LN * E := by
    rw [Real.rpow_def_of_pos (div_pos (by linarith) hp), mul_comm]
    congr 1
    congr 1
    simp only [E, Λ, hcinf]
    rw [Real.log_div (by linarith) hp.ne', Real.log_div hp.ne' hpp.ne',
      Real.log_div (by linarith) hpp.ne']
    ring
  rw [htarget]
  have hlo : Filter.Tendsto (fun n : ℕ => min ((tN n p pp : ℝ) / n)
      ((tN n p pp : ℝ) / n * Real.exp (-(Real.log (p / pp) - Real.log (cc n p pp)) / pp) -
        1 / n)) Filter.atTop (nhds (LN * E)) := by
    have := hN.min ((hN.mul hE).sub hinv)
    rw [sub_zero, min_eq_right] at this
    · exact this
    · nlinarith
  have hhi : Filter.Tendsto (fun n : ℕ => ((tN n p pp : ℝ) / n - 2 * (1 / n)) *
      Real.exp (-(Real.log (p / pp) - Real.log (cc n p pp)) / pp) + 2 * (1 / n)) Filter.atTop
      (nhds (LN * E)) := by
    have := ((hN.sub (hinv.const_mul 2)).mul hE).add (hinv.const_mul 2)
    rw [mul_zero, sub_zero, add_zero] at this
    exact this
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi
  · filter_upwards [Filter.eventually_ge_atTop 1, hev3] with n hn h3
    have hb := (tY_bounds n p pp hn hp0 hp1 hpp0 hpp1 h3).2
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    rw [div_mul_eq_mul_div, ← sub_div, min_div_div_right hnpos.le]
    exact div_le_div_of_nonneg_right hb hnpos.le
  · filter_upwards [Filter.eventually_ge_atTop 1, hev3] with n hn h3
    have hb := (tY_bounds n p pp hn hp0 hp1 hpp0 hpp1 h3).1
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    have : ((tN n p pp : ℝ) / n - 2 * (1 / n)) *
        Real.exp (-(Real.log (p / pp) - Real.log (cc n p pp)) / pp) + 2 * (1 / n) =
        (((tN n p pp : ℝ) - 2) *
          Real.exp (-(Real.log (p / pp) - Real.log (cc n p pp)) / pp) + 2) / n := by
      field_simp
    rw [this]
    exact div_le_div_of_nonneg_right hb hnpos.le
