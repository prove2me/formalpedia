-- Prove2me | solution 1 for SecretaryAdvice.BinaryLimit.opt_eq_greedy_value
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T00:21:07.889955+00:00
-- url     : https://prove2.me/submissions/07ab0ce4-1cae-4dea-ae6a-ff45349e9d3a

import Mathlib
import Definitions.Def_SecretaryAdvice_BinaryLimit_Dual

open SecretaryAdvice.BinaryLimit

namespace SecBinOptEq

theorem stable (n : ℕ) (p pp : ℝ) (a b i : ℕ) (s : Bool) (hab : a ≤ b)
    (hi : n-a < i) : greedyStages n p pp b i s = greedyStages n p pp a i s := by
  induction b, hab using Nat.le_induction with
  | base => rfl
  | succ b hab ih =>
    simp only [greedyStages,if_neg (show i ≠ n-b by omega)]
    exact ih

/-- the future sum -/
noncomputable def F (n : ℕ) (p pp : ℝ) (i : ℕ) : ℝ :=
  ∑ j ∈ Finset.Ioc i n, (w n p pp j true + w n p pp j false)

/-- the objective coefficient `a_s` -/
noncomputable def A (p : ℝ) (s : Bool) : ℝ := if s then p else 1 - p

/-- the dual coefficient `c_s` -/
noncomputable def C (pp : ℝ) (s : Bool) : ℝ := if s then 1 - pp else pp

theorem recurrence (n : ℕ) (p pp : ℝ) (i : ℕ) (hi : 1 ≤ i) (hin : i ≤ n) (s : Bool) :
    w n p pp i s = max 0 (A p s - C pp s / (i : ℝ) * F n p pp i) := by
  have hbase : n-(n-i)=i := by omega
  unfold A C F
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

/-- `d_i` for a primal vector -/
noncomputable def D (pp : ℝ) (z : ℕ → Bool → ℝ) (i : ℕ) : ℝ :=
  (1 / (i : ℝ)) * ((1 - pp) * z i true + pp * z i false)

/-- Exchange of summation: `∑ d_i F_i = ∑_j W_j ∑_{i<j} d_i`. -/
theorem exchange (n : ℕ) (p pp : ℝ) (z : ℕ → Bool → ℝ) :
    ∑ i ∈ Finset.Icc 1 n, D pp z i * F n p pp i =
      ∑ j ∈ Finset.Icc 1 n, (w n p pp j true + w n p pp j false) *
        ∑ i ∈ Finset.Ico 1 j, D pp z i := by
  unfold F
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm' (t' := Finset.Icc 1 n) (s' := fun j => Finset.Ico 1 j)]
  · apply Finset.sum_congr rfl; intro j _; apply Finset.sum_congr rfl; intro i _; ring
  · intro x y
    simp only [Finset.mem_Icc, Finset.mem_Ioc, Finset.mem_Ico]
    omega

/-- per-coordinate inequality `a_s z ≤ w z + c_s/i F z` -/
theorem coord_ineq (n : ℕ) (p pp : ℝ) (i : ℕ) (hi : 1 ≤ i) (hin : i ≤ n) (s : Bool)
    (x : ℝ) (hx : 0 ≤ x) :
    A p s * x ≤ w n p pp i s * x + C pp s / (i : ℝ) * F n p pp i * x := by
  rw [recurrence n p pp i hi hin s, ← add_mul]
  apply mul_le_mul_of_nonneg_right _ hx
  have := le_max_right 0 (A p s - C pp s / (i : ℝ) * F n p pp i)
  linarith

theorem weak (n : ℕ) (p pp : ℝ) (z : ℕ → Bool → ℝ) (hz : PrimalFeasible n p pp z) :
    ∑ i ∈ Finset.Icc 1 n, (p * z i true + (1 - p) * z i false) ≤
      ∑ i ∈ Finset.Icc 1 n, (w n p pp i true + w n p pp i false) := by
  have key : ∀ i ∈ Finset.Icc 1 n, p * z i true + (1 - p) * z i false ≤
      (w n p pp i true + w n p pp i false) * (1 - ∑ j ∈ Finset.Ico 1 i, D pp z j) +
        D pp z i * F n p pp i := by
    intro i hi
    have hi' := Finset.mem_Icc.mp hi
    obtain ⟨hY0, -, hYR⟩ := hz i hi true
    obtain ⟨hN0, -, hNR⟩ := hz i hi false
    have h1 := coord_ineq n p pp i hi'.1 hi'.2 true (z i true) hY0
    have h2 := coord_ineq n p pp i hi'.1 hi'.2 false (z i false) hN0
    simp only [A, C, if_true, Bool.false_eq_true, if_false] at h1 h2
    have hR : ∑ j ∈ Finset.Ico 1 i, D pp z j =
        ∑ j ∈ Finset.Ico 1 i, (1 / (j : ℝ)) * ((1 - pp) * z j true + pp * z j false) := rfl
    rw [← hR] at hYR hNR
    have h3 := mul_le_mul_of_nonneg_left hYR (w_nonneg n p pp i true)
    have h4 := mul_le_mul_of_nonneg_left hNR (w_nonneg n p pp i false)
    have hD : D pp z i * F n p pp i = (1 - pp) / (i : ℝ) * F n p pp i * z i true +
        pp / (i : ℝ) * F n p pp i * z i false := by
      unfold D; ring
    rw [hD]
    nlinarith
  calc _ ≤ ∑ i ∈ Finset.Icc 1 n,
        ((w n p pp i true + w n p pp i false) * (1 - ∑ j ∈ Finset.Ico 1 i, D pp z j) +
          D pp z i * F n p pp i) := Finset.sum_le_sum key
    _ = _ := by
      rw [Finset.sum_add_distrib, exchange, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro j _; ring

/-- indicator of a tight dual constraint -/
noncomputable def E (n : ℕ) (p pp : ℝ) (i : ℕ) (s : Bool) : ℝ :=
  if 0 ≤ A p s - C pp s / (i : ℝ) * F n p pp i then 1 else 0

/-- the remaining mass -/
noncomputable def R (n : ℕ) (p pp : ℝ) : ℕ → ℝ
  | 0 => 1
  | i + 1 => R n p pp i - (1 / (i : ℝ)) *
      ((1 - pp) * E n p pp i true + pp * E n p pp i false) * R n p pp i

/-- the primal solution -/
noncomputable def Z (n : ℕ) (p pp : ℝ) (i : ℕ) (s : Bool) : ℝ := E n p pp i s * R n p pp i

theorem E_nonneg (n : ℕ) (p pp : ℝ) (i : ℕ) (s : Bool) : 0 ≤ E n p pp i s := by
  unfold E; split <;> norm_num

theorem E_le_one (n : ℕ) (p pp : ℝ) (i : ℕ) (s : Bool) : E n p pp i s ≤ 1 := by
  unfold E; split <;> norm_num

theorem R_bounds (n : ℕ) (p pp : ℝ) (hpp0 : 0 ≤ pp) (hpp1 : pp ≤ 1) (i : ℕ) :
    0 ≤ R n p pp i ∧ R n p pp i ≤ 1 := by
  induction i with
  | zero => simp [R]
  | succ i ih =>
    simp only [R]
    have hE1 := E_nonneg n p pp i true
    have hE2 := E_nonneg n p pp i false
    have hE3 := E_le_one n p pp i true
    have hE4 := E_le_one n p pp i false
    have hq0 : 0 ≤ (1 - pp) * E n p pp i true + pp * E n p pp i false := by
      have := mul_nonneg (show 0 ≤ 1 - pp by linarith) hE1
      have := mul_nonneg hpp0 hE2
      linarith
    have hq1 : (1 - pp) * E n p pp i true + pp * E n p pp i false ≤ 1 := by
      have := mul_le_mul_of_nonneg_left hE3 (show 0 ≤ 1 - pp by linarith)
      have := mul_le_mul_of_nonneg_left hE4 hpp0
      linarith
    set q := (1 - pp) * E n p pp i true + pp * E n p pp i false
    rcases Nat.eq_zero_or_pos i with h0 | hpos
    · subst h0; simp only [Nat.cast_zero, div_zero, zero_mul, sub_zero]; exact ih
    · have hi : (1 : ℝ) ≤ i := by exact_mod_cast hpos
      have hf0 : 0 ≤ 1 / (i : ℝ) * q := mul_nonneg (by positivity) hq0
      have hf1 : 1 / (i : ℝ) * q ≤ 1 := by
        rw [one_div_mul_eq_div, div_le_one (by linarith)]; linarith
      constructor
      · nlinarith
      · nlinarith

theorem R_eq (n : ℕ) (p pp : ℝ) (i : ℕ) :
    R n p pp i = 1 - ∑ j ∈ Finset.Ico 1 i, D pp (Z n p pp) j := by
  induction i with
  | zero => simp [R]
  | succ i ih =>
    simp only [R]
    rcases Nat.eq_zero_or_pos i with h0 | hpos
    · subst h0; simp [R]
    · rw [Finset.sum_Ico_succ_top (show 1 ≤ i from hpos)]
      have ih' : ∑ j ∈ Finset.Ico 1 i, D pp (Z n p pp) j = 1 - R n p pp i := by linarith
      rw [ih']
      unfold D Z; ring

theorem achieve (n : ℕ) (p pp : ℝ) :
    ∑ i ∈ Finset.Icc 1 n, (p * Z n p pp i true + (1 - p) * Z n p pp i false) =
      ∑ i ∈ Finset.Icc 1 n, (w n p pp i true + w n p pp i false) := by
  have key : ∀ i ∈ Finset.Icc 1 n, p * Z n p pp i true + (1 - p) * Z n p pp i false =
      (w n p pp i true + w n p pp i false) * (1 - ∑ j ∈ Finset.Ico 1 i, D pp (Z n p pp) j) +
        D pp (Z n p pp) i * F n p pp i := by
    intro i hi
    have hi' := Finset.mem_Icc.mp hi
    rw [← R_eq]
    have hs : ∀ s : Bool, A p s * Z n p pp i s =
        w n p pp i s * R n p pp i + C pp s / (i : ℝ) * F n p pp i * Z n p pp i s := by
      intro s
      rw [recurrence n p pp i hi'.1 hi'.2 s]
      unfold Z E
      split_ifs with h
      · rw [max_eq_right h]; ring
      · rw [max_eq_left (by linarith)]; ring
    have h1 := hs true
    have h2 := hs false
    simp only [A, C, if_true, Bool.false_eq_true, if_false] at h1 h2
    unfold D
    have : 1 / (i : ℝ) * ((1 - pp) * Z n p pp i true + pp * Z n p pp i false) * F n p pp i =
        (1 - pp) / (i : ℝ) * F n p pp i * Z n p pp i true +
          pp / (i : ℝ) * F n p pp i * Z n p pp i false := by ring
    rw [this]
    linarith
  rw [Finset.sum_congr rfl key, Finset.sum_add_distrib, exchange, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro j _; ring

theorem Z_feasible (n : ℕ) (p pp : ℝ) (hpp0 : 0 ≤ pp) (hpp1 : pp ≤ 1) :
    PrimalFeasible n p pp (Z n p pp) := by
  intro i _ s
  have hR := R_bounds n p pp hpp0 hpp1 i
  have hE0 := E_nonneg n p pp i s
  have hE1 := E_le_one n p pp i s
  have hZR : Z n p pp i s ≤ R n p pp i := by
    unfold Z; nlinarith
  refine ⟨mul_nonneg hE0 hR.1, hZR.trans hR.2, ?_⟩
  have := R_eq n p pp i
  unfold D at this
  rw [← this]; exact hZR

end SecBinOptEq

open SecBinOptEq in
theorem solution (n : ℕ) (p pp : ℝ) (hn : 1 ≤ n) (hp0 : (1 / 2 : ℝ) ≤ p) (hp1 : p ≤ 1) (hpp0 : (1 / 2 : ℝ) ≤ pp) (hpp1 : pp ≤ 1) :
    Opt n p pp = (1 / (n : ℝ)) *
      (∑ i ∈ Finset.Icc 1 n, (w n p pp i true + w n p pp i false)) := by
  have hobj : ∀ z : ℕ → Bool → ℝ, primalObj n p pp z =
      (1 / (n : ℝ)) * ∑ i ∈ Finset.Icc 1 n, (p * z i true + (1 - p) * z i false) := by
    intro z; unfold primalObj; rw [Finset.mul_sum]
  have hnpos : (0 : ℝ) < 1 / (n : ℝ) := by
    have : (0 : ℝ) < n := by exact_mod_cast hn
    positivity
  apply IsGreatest.csSup_eq
  constructor
  · refine ⟨Z n p pp, Z_feasible n p pp (by linarith) hpp1, ?_⟩
    rw [hobj, achieve]
  · rintro _ ⟨z, hz, rfl⟩
    rw [hobj]
    exact mul_le_mul_of_nonneg_left (weak n p pp z hz) hnpos.le
