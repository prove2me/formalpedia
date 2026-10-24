-- Prove2me | solution 1 for SecretaryAdvice.BinaryLimit.tN_limit
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T00:23:55.007002+00:00
-- url     : https://prove2.me/submissions/aecd0f2f-de72-4194-972c-efb5aaed437d

import Mathlib
import Definitions.Def_SecretaryAdvice_BinaryLimit_Dual
import Theorems.Thm_SecretaryAdvice_BinaryLimit_dual_closed_form_late

open SecretaryAdvice.BinaryLimit

namespace SecBinTN

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
    (2 ≤ tN n p pp → 1 - p ≤ pp * H n (tN n p pp - 1)) := by
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
  linarith

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

end SecBinTN

open SecBinTN in
theorem solution (p pp : ℝ) (hp0 : (1 / 2 : ℝ) ≤ p) (hp1 : p ≤ 1) (hpp0 : (1 / 2 : ℝ) ≤ pp) (hpp1 : pp ≤ 1) :
    Filter.Tendsto (fun n : ℕ => (tN n p pp : ℝ) / (n : ℝ)) Filter.atTop
      (nhds (Real.exp (p / pp - 1 / pp))) := by
  have hinv : Filter.Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ)) Filter.atTop (nhds 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have hpp : 0 < pp := by linarith
  rcases hp1.lt_or_eq with hp1' | hp1'
  · set α := (1 - p) / pp with hα
    have hαpos : 0 < α := div_pos (by linarith) hpp
    have hexp : p / pp - 1 / pp = -α := by rw [hα]; field_simp; ring
    rw [hexp]
    set L := Real.exp (-α)
    have hhi : Filter.Tendsto (fun n : ℕ => L + 2 * (1 / (n : ℝ))) Filter.atTop (nhds L) := by
      simpa using (hinv.const_mul 2).const_add L
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hhi
    · filter_upwards [Filter.eventually_ge_atTop 1] with n hn
      have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
      obtain ⟨hT1, hTn, -, hpos⟩ := tN_props n p pp
      -- `T ≤ n` because `w_n^N = 1 - p > 0`
      have hT : tN n p pp ≤ n := by
        by_contra hne
        have hzero := (tN_props n p pp).2.2.1 n hn (by omega)
        rw [recurrence n p pp n hn le_rfl false] at hzero
        simp only [Bool.false_eq_true, if_false] at hzero
        have : F n p pp n = 0 := by unfold F; simp
        unfold F at this
        rw [this, mul_zero, sub_zero] at hzero
        have := max_eq_left_iff.mp hzero
        linarith
      have ha := (tN_char n p pp hn hp0 hp1 hpp0 hpp1 hT).1
      have hl := H_lower n (tN n p pp) hT1 hT
      have hTpos : (0 : ℝ) < tN n p pp := by exact_mod_cast hT1
      have h1 : Real.log n < Real.log (tN n p pp) + α := by
        have : H n (tN n p pp) < α := by rw [hα, lt_div_iff₀ hpp]; linarith
        linarith
      have h2 : (n : ℝ) < tN n p pp * Real.exp α := by
        have := Real.exp_lt_exp.mpr h1
        rwa [Real.exp_add, Real.exp_log hnpos, Real.exp_log hTpos] at this
      rw [le_div_iff₀ hnpos]
      have := Real.exp_pos α
      have hm : Real.exp (-α) * Real.exp α = 1 := by rw [← Real.exp_add]; simp
      nlinarith [Real.exp_pos (-α)]
    · filter_upwards [Filter.eventually_ge_atTop 1] with n hn
      have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
      obtain ⟨hT1, hTn, -, -⟩ := tN_props n p pp
      rw [div_le_iff₀ hnpos]
      have hgoal : (tN n p pp : ℝ) ≤ L * n + 2 := by
        rcases Nat.lt_or_ge (tN n p pp) 3 with h3 | h3
        · have : (tN n p pp : ℝ) ≤ 2 := by exact_mod_cast (show tN n p pp ≤ 2 by omega)
          have := Real.exp_pos (-α)
          nlinarith
        · have hT : tN n p pp ≤ n := by
            by_contra hne
            have hzero := (tN_props n p pp).2.2.1 n hn (by omega)
            rw [recurrence n p pp n hn le_rfl false] at hzero
            simp only [Bool.false_eq_true, if_false] at hzero
            have : F n p pp n = 0 := by unfold F; simp
            unfold F at this
            rw [this, mul_zero, sub_zero] at hzero
            have := max_eq_left_iff.mp hzero
            linarith
          have hb := (tN_char n p pp hn hp0 hp1 hpp0 hpp1 hT).2 (by omega)
          have hu := H_upper n (tN n p pp - 1) (by omega) (by omega)
          have hαle : α ≤ H n (tN n p pp - 1) := by rw [hα, div_le_iff₀ hpp]; linarith
          rw [Nat.cast_sub (by omega)] at hu
          push_cast at hu
          have hT2 : (0 : ℝ) < (tN n p pp : ℝ) - 1 - 1 := by
            have : (3 : ℝ) ≤ tN n p pp := by exact_mod_cast h3
            linarith
          have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by
            have : (3 : ℝ) ≤ n := by exact_mod_cast (le_trans h3 hT)
            linarith
          have h1 : Real.log ((tN n p pp : ℝ) - 1 - 1) + α ≤ Real.log ((n : ℝ) - 1) := by linarith
          have h2 := Real.exp_le_exp.mpr h1
          rw [Real.exp_add, Real.exp_log hT2, Real.exp_log hn1] at h2
          have hm : Real.exp (-α) * Real.exp α = 1 := by rw [← Real.exp_add]; simp
          have hL : 0 < L := Real.exp_pos _
          have h3' : ((tN n p pp : ℝ) - 1 - 1) ≤ L * ((n : ℝ) - 1) := by
            have := mul_le_mul_of_nonneg_left h2 hL.le
            nlinarith
          nlinarith
      have : (L + 2 * (1 / (n : ℝ))) * n = L * n + 2 := by field_simp
      rw [this]; exact hgoal
  · subst hp1'
    have hexp : 1 / pp - 1 / pp = (0 : ℝ) := by ring
    rw [hexp, Real.exp_zero]
    have h : Filter.Tendsto (fun n : ℕ => (1 : ℝ) + 1 / (n : ℝ)) Filter.atTop (nhds 1) := by
      simpa using hinv.const_add 1
    apply h.congr'
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    rw [tN_p_one n pp hpp.le]
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    push_cast
    field_simp
