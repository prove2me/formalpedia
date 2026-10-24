-- Prove2me | solution 1 for SecretaryAdvice.BinaryLimit.theorem_20
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T00:19:05.442755+00:00
-- url     : https://prove2.me/submissions/63723589-6ba5-4ae9-a62d-e4c5866eefd5

import Mathlib
import Definitions.Def_SecretaryAdvice_BinaryLimit_Dual
import Theorems.Thm_SecretaryAdvice_BinaryLimit_opt_eq_greedy_value
import Theorems.Thm_SecretaryAdvice_BinaryLimit_tY_limit
import Theorems.Thm_SecretaryAdvice_BinaryLimit_tN_limit
import Theorems.Thm_SecretaryAdvice_BinaryLimit_thresholds_ordered

open SecretaryAdvice.BinaryLimit

namespace SecBinT20

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

/-- Bounds in the case `pp < 1`, through the `Y` threshold. -/
theorem bounds_Y (n : ℕ) (p pp : ℝ) (hn : 1 ≤ n) (hp0 : (1 / 2 : ℝ) ≤ p) (hp1 : p ≤ 1)
    (hpp0 : (1 / 2 : ℝ) ≤ pp) (hpp1 : pp < 1) :
    p / (1 - pp) * ((tY n p pp : ℝ) - 1) ≤ (n : ℝ) * Opt n p pp ∧
    (n : ℝ) * Opt n p pp ≤ p / (1 - pp) * (tY n p pp : ℝ) + 1 := by
  obtain ⟨hT1, hTn, hzero, hpos⟩ := tY_props n p pp
  obtain ⟨-, -, hzeroN, -⟩ := tN_props n p pp
  have hord := thresholds_ordered n p pp hn hp0 hp1 hpp0 hpp1.le
  set T := tY n p pp with hTdef
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hOpt : (n : ℝ) * Opt n p pp = F n p pp (T - 1) := by
    rw [opt_eq_greedy_value n p pp hn hp0 hp1 hpp0 hpp1.le, ← mul_assoc,
      mul_one_div_cancel hnpos.ne', one_mul, split_sum n p pp (T - 1) (by omega)]
    rw [Finset.sum_eq_zero, zero_add]
    intro j hj
    rw [Finset.mem_Icc] at hj
    rw [hzero j hj.1 (by omega), hzeroN j hj.1 (by omega), add_zero]
  have hc : 0 < 1 - pp := by linarith
  have hp : 0 < p := by linarith
  rw [hOpt]
  constructor
  · -- lower bound
    rcases Nat.lt_or_ge T 2 with hT2 | hT2
    · have : T = 1 := by omega
      rw [this]; simp only [Nat.cast_one, sub_self, mul_zero]
      exact F_nonneg ..
    · have hw := hzero (T - 1) (by omega) (by omega)
      rw [recurrence n p pp (T - 1) (by omega) (by omega) true] at hw
      simp only [if_true] at hw
      have hle := (max_eq_left_iff.mp hw)
      change p - (1 - pp) / ((T - 1 : ℕ) : ℝ) * F n p pp (T - 1) ≤ 0 at hle
      have hcast : ((T - 1 : ℕ) : ℝ) = (T : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega)]; simp
      rw [hcast] at hle
      have hT' : (0 : ℝ) < (T : ℝ) - 1 := by
        have : (2 : ℝ) ≤ T := by exact_mod_cast hT2
        linarith
      rw [div_mul_eq_mul_div, sub_nonpos, le_div_iff₀ hT'] at hle
      rw [div_mul_eq_mul_div, div_le_iff₀ hc]
      linarith
  · -- upper bound
    rcases Nat.lt_or_ge n T with hTn' | hTn'
    · have : T - 1 = n := by omega
      rw [this]
      have : F n p pp n = 0 := by unfold F; simp
      rw [this]
      positivity
    · have hw := hpos hTn'
      rw [recurrence n p pp T (by omega) hTn' true] at hw
      simp only [if_true] at hw
      have hlt : 0 < p - (1 - pp) / (T : ℝ) * F n p pp T := by
        rcases lt_max_iff.mp hw with h | h
        · exact absurd h (lt_irrefl 0)
        · exact h
      have hTpos : (0 : ℝ) < T := by exact_mod_cast hT1
      rw [div_mul_eq_mul_div, sub_pos, div_lt_iff₀ hTpos] at hlt
      rw [F_pred n p pp T hT1 hTn']
      have hW := W_le_one n p pp (by linarith) hpp1.le hp.le hp1 T hT1 hTn'
      have : F n p pp T ≤ p / (1 - pp) * T := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hc]; linarith
      linarith

/-- Bounds in the case `pp = 1`, through the `N` threshold. -/
theorem bounds_N (n : ℕ) (p : ℝ) (hn : 1 ≤ n) (hp0 : (1 / 2 : ℝ) ≤ p) (hp1 : p ≤ 1) :
    (tN n p 1 : ℝ) - 1 ≤ (n : ℝ) * Opt n p 1 ∧
    (n : ℝ) * Opt n p 1 ≤ (tN n p 1 : ℝ) + 1 := by
  obtain ⟨hT1, hTn, hzeroN, hpos⟩ := tN_props n p 1
  set T := tN n p 1 with hTdef
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hY : ∀ j, 1 ≤ j → j ≤ n → w n p 1 j true = p := by
    intro j hj hjn
    rw [recurrence n p 1 j hj hjn true]
    simp only [if_true, sub_self, zero_div, zero_mul, sub_zero]
    exact max_eq_right (by linarith)
  have hOpt : (n : ℝ) * Opt n p 1 = p * ((T : ℝ) - 1) + F n p 1 (T - 1) := by
    rw [opt_eq_greedy_value n p 1 hn hp0 hp1 (by norm_num) le_rfl, ← mul_assoc,
      mul_one_div_cancel hnpos.ne', one_mul, split_sum n p 1 (T - 1) (by omega)]
    congr 1
    rw [Finset.sum_congr rfl (g := fun _ => p)]
    · simp only [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
      rw [show T - 1 + 1 - 1 = T - 1 by omega, Nat.cast_sub hT1]
      push_cast; ring
    · intro j hj
      rw [Finset.mem_Icc] at hj
      rw [hY j hj.1 (by omega), hzeroN j hj.1 (by omega), add_zero]
  have hp : 0 < p := by linarith
  rw [hOpt]
  constructor
  · rcases Nat.lt_or_ge T 2 with hT2 | hT2
    · have : T = 1 := by omega
      rw [this]; simp only [Nat.cast_one, sub_self, mul_zero, zero_add]
      exact F_nonneg ..
    · have hw := hzeroN (T - 1) (by omega) (by omega)
      rw [recurrence n p 1 (T - 1) (by omega) (by omega) false] at hw
      simp only [Bool.false_eq_true, if_false] at hw
      have hle := (max_eq_left_iff.mp hw)
      have hcast : ((T - 1 : ℕ) : ℝ) = (T : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega)]; simp
      rw [hcast] at hle
      have hT' : (0 : ℝ) < (T : ℝ) - 1 := by
        have : (2 : ℝ) ≤ T := by exact_mod_cast hT2
        linarith
      rw [div_mul_eq_mul_div, sub_nonpos, le_div_iff₀ hT', one_mul] at hle
      change (1 - p) * ((T : ℝ) - 1) ≤ F n p 1 (T - 1) at hle
      nlinarith
  · rcases Nat.lt_or_ge n T with hTn' | hTn'
    · have : T - 1 = n := by omega
      rw [this]
      have : F n p 1 n = 0 := by unfold F; simp
      rw [this]
      have : (n : ℝ) + 1 ≤ T := by
        have : n + 1 ≤ T := hTn'
        exact_mod_cast this
      nlinarith
    · have hw := hpos hTn'
      rw [recurrence n p 1 T (by omega) hTn' false] at hw
      simp only [Bool.false_eq_true, if_false] at hw
      have hlt : 0 < 1 - p - 1 / (T : ℝ) * F n p 1 T := by
        rcases lt_max_iff.mp hw with h | h
        · exact absurd h (lt_irrefl 0)
        · exact h
      have hTpos : (0 : ℝ) < T := by exact_mod_cast hT1
      rw [div_mul_eq_mul_div, one_mul, sub_pos, div_lt_iff₀ hTpos] at hlt
      rw [F_pred n p 1 T hT1 hTn']
      have hW := W_le_one n p 1 (by norm_num) le_rfl hp.le hp1 T hT1 hTn'
      have h1 : (1 : ℝ) ≤ T := by exact_mod_cast hT1
      nlinarith

end SecBinT20

open SecBinT20 in
theorem solution (p pp : ℝ) (hp0 : (1 / 2 : ℝ) ≤ p) (hp1 : p ≤ 1) (hpp0 : (1 / 2 : ℝ) ≤ pp) (hpp1 : pp ≤ 1) :
    Filter.Tendsto (fun n : ℕ => Opt n p pp) Filter.atTop (nhds (limitValue p pp)) := by
  have hinv : Filter.Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ)) Filter.atTop (nhds 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  rcases hpp1.lt_or_eq with hpp1 | hpp1
  · have hY := tY_limit p pp hp0 hp1 hpp0 hpp1.le
    set L := ((1 - pp) / p) ^ (1 / pp) * Real.exp (p / pp - 1 / pp)
    set c := p / (1 - pp)
    have hc : 0 < 1 - pp := by linarith
    have hp : 0 < p := by linarith
    have hlim : c * L = limitValue p pp := by
      unfold limitValue
      have hr : 0 < (1 - pp) / p := div_pos hc hp
      have : c = ((1 - pp) / p) ^ (-1 : ℝ) := by
        rw [Real.rpow_neg_one, inv_div]
      rw [this, ← mul_assoc, ← Real.rpow_add hr]
      congr 2
      field_simp
      ring
    rw [← hlim]
    have hlo : Filter.Tendsto (fun n : ℕ => c * ((tY n p pp : ℝ) / n - 1 / n)) Filter.atTop
        (nhds (c * L)) := by
      have := (hY.sub hinv).const_mul c
      simpa using this
    have hhi : Filter.Tendsto (fun n : ℕ => c * ((tY n p pp : ℝ) / n) + 1 / n) Filter.atTop
        (nhds (c * L)) := by
      have := (hY.const_mul c).add hinv
      simpa using this
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi
    · filter_upwards [Filter.eventually_ge_atTop 1] with n hn
      have hb := (bounds_Y n p pp hn hp0 hp1 hpp0 hpp1).1
      have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
      rw [← sub_div, mul_div_assoc', div_le_iff₀ hnpos]
      linarith
    · filter_upwards [Filter.eventually_ge_atTop 1] with n hn
      have hb := (bounds_Y n p pp hn hp0 hp1 hpp0 hpp1).2
      have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
      rw [mul_div_assoc', ← add_div, le_div_iff₀ hnpos]
      linarith
  · subst hpp1
    have hN := tN_limit p 1 hp0 hp1 hpp0 le_rfl
    have hlim : Real.exp (p / 1 - 1 / 1) = limitValue p 1 := by
      unfold limitValue
      simp
    rw [← hlim]
    have hlo : Filter.Tendsto (fun n : ℕ => (tN n p 1 : ℝ) / n - 1 / n) Filter.atTop
        (nhds (Real.exp (p / 1 - 1 / 1))) := by
      simpa using hN.sub hinv
    have hhi : Filter.Tendsto (fun n : ℕ => (tN n p 1 : ℝ) / n + 1 / n) Filter.atTop
        (nhds (Real.exp (p / 1 - 1 / 1))) := by
      simpa using hN.add hinv
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi
    · filter_upwards [Filter.eventually_ge_atTop 1] with n hn
      have hb := (bounds_N n p hn hp0 hp1).1
      have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
      rw [← sub_div, div_le_iff₀ hnpos]
      linarith
    · filter_upwards [Filter.eventually_ge_atTop 1] with n hn
      have hb := (bounds_N n p hn hp0 hp1).2
      have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
      rw [← add_div, le_div_iff₀ hnpos]
      linarith
