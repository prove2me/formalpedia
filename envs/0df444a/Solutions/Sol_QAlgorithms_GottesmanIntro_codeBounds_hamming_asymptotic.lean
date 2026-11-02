-- Prove2me | solution 1 for QAlgorithms.GottesmanIntro.codeBounds_hamming_asymptotic
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T19:55:39.763857+00:00
-- url     : https://prove2.me/submissions/b0453c0b-e101-47ab-bf5e-3b7664e82cce

import Definitions.Def_QAlgorithms_Defs_FTCircuit
set_option autoImplicit false
open QAlgorithms QAlgorithms.Stabilizer
open scoped Matrix

private lemma linear_entropy_identity (q n j : ℝ) :
    j * Real.log 3 - j * Real.log q - (n - j) * Real.log (1 - q) =
      n * (q * Real.log 3 + Real.binEntropy q) +
        (j - q * n) * (Real.log 3 - Real.log q + Real.log (1 - q)) := by
  rw [Real.binEntropy, Real.log_inv, Real.log_inv]
  ring

private lemma rate_mul_log_two (q : ℝ) :
    (1 - q * Real.logb 2 3 - binEntropy2 q) * Real.log 2 =
      Real.log 2 - (q * Real.log 3 + Real.binEntropy q) := by
  have h2 : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  rw [binEntropy2, Real.logb]
  field_simp [h2]
  ring

private lemma log_three_sub_log_add_log_nonneg {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (hq3 : q ≤ 3 * (1 - q)) :
    0 ≤ Real.log 3 - Real.log q + Real.log (1 - q) := by
  have h1q : 0 < 1 - q := by linarith
  have hle : Real.log q ≤ Real.log (3 * (1 - q)) := Real.log_le_log hq0 hq3
  rw [Real.log_mul (by norm_num) h1q.ne'] at hle
  linarith

noncomputable def binomTerm (n : ℕ) (p : ℝ) (i : ℕ) : ℝ :=
  p ^ i * (1 - p) ^ (n - i) * (n.choose i : ℝ)

private lemma binomTerm_step {n i : ℕ} (hi : i < n) (p : ℝ) :
    (1 - p) * (i + 1 : ℝ) * binomTerm n p (i + 1) =
      p * (n - i : ℝ) * binomTerm n p i := by
  unfold binomTerm
  have hchoose : (n.choose (i + 1) : ℝ) * ((i + 1 : ℕ) : ℝ) = (n.choose i : ℝ) * ((n - i : ℕ) : ℝ) := by
    exact_mod_cast Nat.choose_succ_right_eq n i
  have hsub : n - i = (n - (i + 1)) + 1 := by omega
  have hcast : ((n - i : ℕ) : ℝ) = (n : ℝ) - (i : ℝ) := Nat.cast_sub hi.le
  have hcast1 : ((i + 1 : ℕ) : ℝ) = (i : ℝ) + 1 := by push_cast; rfl
  rw [hcast1, hcast] at hchoose
  calc (1 - p) * ((i : ℝ) + 1) * (p ^ (i + 1) * (1 - p) ^ (n - (i + 1)) * (n.choose (i + 1) : ℝ))
    _ = p ^ (i + 1) * ((1 - p) ^ (n - (i + 1)) * (1 - p) ^ 1) * ((n.choose (i + 1) : ℝ) * ((i : ℝ) + 1)) := by ring
    _ = p ^ (i + 1) * (1 - p) ^ (n - i) * ((n.choose i : ℝ) * ((n : ℝ) - (i : ℝ))) := by
        rw [← pow_add, ← hsub, hchoose]
    _ = p * ((n : ℝ) - (i : ℝ)) * (p ^ i * (1 - p) ^ (n - i) * (n.choose i : ℝ)) := by
        rw [pow_succ]; ring

private lemma binomTerm_le_of_lt_floor {n i : ℕ} (hi : i < n) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (him : i < ⌊p * (n + 1 : ℝ)⌋₊) :
    binomTerm n p i ≤ binomTerm n p (i + 1) := by
  have h1p : 0 < 1 - p := by linarith
  have hi1_le : (i + 1 : ℕ) ≤ ⌊p * (n + 1 : ℝ)⌋₊ := him
  have hi1_real : ((i + 1 : ℕ) : ℝ) ≤ p * (n + 1 : ℝ) :=
    (Nat.cast_le.mpr hi1_le).trans (Nat.floor_le (by positivity))
  push_cast at hi1_real
  have Nineq : (1 - p) * ((i : ℝ) + 1) ≤ p * ((n : ℝ) - (i : ℝ)) := by linarith
  have hpos : 0 < (1 - p) * ((i : ℝ) + 1) := by positivity
  have hstep := binomTerm_step hi p
  have hnonneg : 0 ≤ binomTerm n p i := by unfold binomTerm; positivity
  have hle : (1 - p) * ((i : ℝ) + 1) * binomTerm n p i ≤
      (1 - p) * ((i : ℝ) + 1) * binomTerm n p (i + 1) := by
    rw [hstep]
    exact mul_le_mul_of_nonneg_right Nineq hnonneg
  exact le_of_mul_le_mul_left hle hpos

private lemma binomTerm_ge_of_floor_le {n i : ℕ} (hi : i < n) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hmi : ⌊p * (n + 1 : ℝ)⌋₊ ≤ i) :
    binomTerm n p (i + 1) ≤ binomTerm n p i := by
  have h1p : 0 < 1 - p := by linarith
  have hlt : p * (n + 1 : ℝ) < (⌊p * (n + 1 : ℝ)⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  have hle : (⌊p * (n + 1 : ℝ)⌋₊ : ℝ) ≤ (i : ℝ) := Nat.cast_le.mpr hmi
  have Nineq : p * ((n : ℝ) - (i : ℝ)) ≤ (1 - p) * ((i : ℝ) + 1) := by linarith
  have hpos : 0 < (1 - p) * ((i : ℝ) + 1) := by positivity
  have hstep := binomTerm_step hi p
  have hnonneg : 0 ≤ binomTerm n p i := by unfold binomTerm; positivity
  have hle2 : (1 - p) * ((i : ℝ) + 1) * binomTerm n p (i + 1) ≤
      (1 - p) * ((i : ℝ) + 1) * binomTerm n p i := by
    rw [hstep]
    exact mul_le_mul_of_nonneg_right Nineq hnonneg
  exact le_of_mul_le_mul_left hle2 hpos

private lemma binomTerm_le_mode_of_le {n : ℕ} {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hm_le : ⌊p * (n + 1 : ℝ)⌋₊ ≤ n) (k i : ℕ) (hik : i + k = ⌊p * (n + 1 : ℝ)⌋₊) :
    binomTerm n p i ≤ binomTerm n p ⌊p * (n + 1 : ℝ)⌋₊ := by
  induction k generalizing i with
  | zero =>
    rw [Nat.add_zero] at hik
    rw [hik]
  | succ k ih =>
    have hi_lt_m : i < ⌊p * (n + 1 : ℝ)⌋₊ := by omega
    have hi_lt_n : i < n := by omega
    exact (binomTerm_le_of_lt_floor hi_lt_n hp0 hp1 hi_lt_m).trans
      (ih (i + 1) (by omega))

private lemma binomTerm_le_mode_of_ge {n : ℕ} {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (k : ℕ) (hk : ⌊p * (n + 1 : ℝ)⌋₊ + k ≤ n) :
    binomTerm n p (⌊p * (n + 1 : ℝ)⌋₊ + k) ≤ binomTerm n p ⌊p * (n + 1 : ℝ)⌋₊ := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hmk_lt_n : ⌊p * (n + 1 : ℝ)⌋₊ + k < n := by omega
    exact (binomTerm_ge_of_floor_le hmk_lt_n hp0 hp1 (Nat.le_add_right _ k)).trans
      (ih (by omega))

private lemma binomTerm_le_mode {n : ℕ} {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hm_le : ⌊p * (n + 1 : ℝ)⌋₊ ≤ n) (i : ℕ) (hi : i ≤ n) :
    binomTerm n p i ≤ binomTerm n p ⌊p * (n + 1 : ℝ)⌋₊ := by
  by_cases him : i ≤ ⌊p * (n + 1 : ℝ)⌋₊
  · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le him
    exact binomTerm_le_mode_of_le hp0 hp1 hm_le k i hk.symm
  · have hmi : ⌊p * (n + 1 : ℝ)⌋₊ ≤ i := by omega
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hmi
    rw [hk]
    exact binomTerm_le_mode_of_ge hp0 hp1 k (by omega)

private lemma one_le_mode_binomTerm {n : ℕ} {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hm_le : ⌊p * (n + 1 : ℝ)⌋₊ ≤ n) :
    1 ≤ (n + 1 : ℝ) * binomTerm n p ⌊p * (n + 1 : ℝ)⌋₊ := by
  have hsum : ∑ i ∈ Finset.range (n + 1), binomTerm n p i = 1 := by
    unfold binomTerm
    rw [← add_pow]
    ring
  refine le_trans (le_of_eq hsum.symm) ?_
  calc ∑ i ∈ Finset.range (n + 1), binomTerm n p i
    _ ≤ ∑ _i ∈ Finset.range (n + 1), binomTerm n p ⌊p * (n + 1 : ℝ)⌋₊ := by
        refine Finset.sum_le_sum fun i hi => ?_
        exact binomTerm_le_mode hp0 hp1 hm_le i (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
    _ = (n + 1 : ℝ) * binomTerm n p ⌊p * (n + 1 : ℝ)⌋₊ := by
        simp [Finset.sum_const, Finset.card_range]

private lemma one_sub_p_le_pred_mode_binomTerm {n : ℕ} (hn : 1 ≤ n) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hm_pos : 1 ≤ ⌊p * (n + 1 : ℝ)⌋₊) (hm_le : ⌊p * (n + 1 : ℝ)⌋₊ ≤ n) :
    1 - p ≤ (n + 1 : ℝ) ^ 2 * binomTerm n p (⌊p * (n + 1 : ℝ)⌋₊ - 1) := by
  set m := ⌊p * (n + 1 : ℝ)⌋₊
  set j₀ := m - 1
  have hj₀_add : j₀ + 1 = m := Nat.sub_add_cancel hm_pos
  have hj₀_lt_n : j₀ < n := by omega
  have hstep := binomTerm_step hj₀_lt_n p
  rw [hj₀_add] at hstep
  have h1p : 0 < 1 - p := by linarith
  have hm_real : (1 : ℝ) ≤ (j₀ : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) j₀]
  have hbm_nonneg : 0 ≤ binomTerm n p m := by unfold binomTerm; positivity
  have hbj_nonneg : 0 ≤ binomTerm n p j₀ := by unfold binomTerm; positivity
  have hle1 : (1 - p) * binomTerm n p m ≤ (n : ℝ) * binomTerm n p j₀ := by
    calc (1 - p) * binomTerm n p m
      _ = (1 - p) * 1 * binomTerm n p m := by ring
      _ ≤ (1 - p) * ((j₀ : ℝ) + 1) * binomTerm n p m := by
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm_real h1p.le) hbm_nonneg
      _ = p * ((n : ℝ) - (j₀ : ℝ)) * binomTerm n p j₀ := hstep
      _ ≤ 1 * (n : ℝ) * binomTerm n p j₀ := by
          have : p * ((n : ℝ) - (j₀ : ℝ)) ≤ 1 * (n : ℝ) := by
            nlinarith [Nat.cast_nonneg (α := ℝ) j₀, show (0 : ℝ) ≤ n by positivity]
          exact mul_le_mul_of_nonneg_right this hbj_nonneg
      _ = (n : ℝ) * binomTerm n p j₀ := by ring
  have hmode := one_le_mode_binomTerm hp0 hp1 hm_le
  calc 1 - p
    _ ≤ (1 - p) * ((n + 1 : ℝ) * binomTerm n p m) := by nlinarith
    _ = (n + 1 : ℝ) * ((1 - p) * binomTerm n p m) := by ring
    _ ≤ (n + 1 : ℝ) * ((n : ℝ) * binomTerm n p j₀) :=
        mul_le_mul_of_nonneg_left hle1 (by positivity)
    _ ≤ (n + 1 : ℝ) * ((n + 1 : ℝ) * binomTerm n p j₀) := by nlinarith
    _ = (n + 1 : ℝ) ^ 2 * binomTerm n p j₀ := by ring

private lemma log_le_two_sqrt (x : ℝ) (hx : 0 < x) :
    Real.log x ≤ 2 * Real.sqrt x := by
  have hsqrt_pos : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have hlog : Real.log x = 2 * Real.log (Real.sqrt x) := by
    rw [Real.log_sqrt hx.le]
    ring
  have hle : Real.log (Real.sqrt x) ≤ Real.sqrt x - 1 :=
    Real.log_le_sub_one_of_pos hsqrt_pos
  linarith

theorem solution
    (hamming : ∀ (n k d : ℕ) (C : Submodule ℂ (EuclideanSpace ℂ (Qubits n))), IsQCode n k d C →
      IsNondegenerate C ((d - 1) / 2) →
      (∑ j ∈ Finset.range ((d - 1) / 2 + 1), 3 ^ j * n.choose j) * 2 ^ k ≤ 2 ^ n) :
    ∀ p : ℝ, 0 < p → p < 1 / 2 → ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N,
      ∀ (k d : ℕ) (C : Submodule ℂ (EuclideanSpace ℂ (Qubits n))), IsQCode n k d C →
        IsNondegenerate C ((d - 1) / 2) → 2 * p * n ≤ d →
        (k : ℝ) / n ≤ 1 - p * Real.logb 2 3 - binEntropy2 p + ε := by
  intro p hp0 hp12 ε hε
  have hp1 : p < 1 := by linarith
  have h1p : 0 < 1 - p := by linarith
  have hp3 : p ≤ 3 * (1 - p) := by linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hC_ent_nonneg : 0 ≤ Real.log 3 - Real.log p + Real.log (1 - p) :=
    log_three_sub_log_add_log_nonneg hp0 hp1 hp3
  set K_const := 2 * (Real.log 3 - Real.log p + Real.log (1 - p)) - Real.log (1 - p) + 8
  have hK_pos : 0 < K_const := by
    have : Real.log (1 - p) < 0 := Real.log_neg h1p (by linarith)
    linarith
  set N := max (max 2 (⌈1 / p⌉₊ + 1)) (⌈(K_const / (ε * Real.log 2)) ^ 2⌉₊ + 1)
  refine ⟨N, fun n hn k d C hC hnd h2pn => ?_⟩
  have hn2 : 2 ≤ n := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hn)
  have hn_p : ⌈1 / p⌉₊ + 1 ≤ n := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hn)
  have hn_K : ⌈(K_const / (ε * Real.log 2)) ^ 2⌉₊ + 1 ≤ n :=
    le_trans (le_max_right _ _) hn
  have hn_pos : (0 : ℝ) < n := by positivity
  set m := ⌊p * (n + 1 : ℝ)⌋₊
  set j₀ := m - 1
  have hm_pos : 1 ≤ m := by
    rw [Nat.one_le_floor_iff]
    have h1 : 1 / p ≤ (n : ℝ) := (Nat.le_ceil (1 / p)).trans (by exact_mod_cast (by omega : ⌈1 / p⌉₊ ≤ n))
    have h2 : 1 ≤ (n : ℝ) * p := (div_le_iff₀ hp0).mp h1
    linarith
  have hm_le : m ≤ n := by
    have hn2_real : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
    have hlt : p * (n + 1 : ℝ) < (n : ℝ) := by nlinarith
    exact Nat.floor_le_of_le hlt.le
  have hj₀_add : j₀ + 1 = m := Nat.sub_add_cancel hm_pos
  have hj₀_le_n : j₀ ≤ n := by omega
  have hj₀_le_t : j₀ ≤ (d - 1) / 2 := by
    have hm_real : (m : ℝ) ≤ p * ((n : ℝ) + 1) := Nat.floor_le (by positivity)
    have h2m : 2 * (m : ℝ) < (d : ℝ) + 1 := by linarith
    have h2m_nat : 2 * m < d + 1 := by exact_mod_cast h2m
    omega
  have hham := hamming n k d C hC hnd
  have hj₀_mem : j₀ ∈ Finset.range ((d - 1) / 2 + 1) := Finset.mem_range.mpr (by omega)
  have hsingle : 3 ^ j₀ * n.choose j₀ ≤ ∑ j ∈ Finset.range ((d - 1) / 2 + 1), 3 ^ j * n.choose j :=
    Finset.single_le_sum (f := fun j => 3 ^ j * n.choose j) (fun j _ => Nat.zero_le _) hj₀_mem
  have hterm_le : (3 ^ j₀ * n.choose j₀) * 2 ^ k ≤ 2 ^ n :=
    (Nat.mul_le_mul_right (2 ^ k) hsingle).trans hham
  have hterm_real : (3 : ℝ) ^ j₀ * (n.choose j₀ : ℝ) * (2 : ℝ) ^ k ≤ (2 : ℝ) ^ n := by
    exact_mod_cast hterm_le
  have hpred := one_sub_p_le_pred_mode_binomTerm (by omega) hp0 hp1 hm_pos hm_le
  change 1 - p ≤ (n + 1 : ℝ) ^ 2 * (p ^ j₀ * (1 - p) ^ (n - j₀) * (n.choose j₀ : ℝ)) at hpred
  have Nineq1 : (1 - p) * (3 : ℝ) ^ j₀ * (2 : ℝ) ^ k ≤
      (n + 1 : ℝ) ^ 2 * p ^ j₀ * (1 - p) ^ (n - j₀) * (2 : ℝ) ^ n := by
    have hpos32 : 0 ≤ (3 : ℝ) ^ j₀ * (2 : ℝ) ^ k := by positivity
    calc (1 - p) * (3 : ℝ) ^ j₀ * (2 : ℝ) ^ k
      _ = (1 - p) * ((3 : ℝ) ^ j₀ * (2 : ℝ) ^ k) := by ring
      _ ≤ ((n + 1 : ℝ) ^ 2 * (p ^ j₀ * (1 - p) ^ (n - j₀) * (n.choose j₀ : ℝ))) *
            ((3 : ℝ) ^ j₀ * (2 : ℝ) ^ k) := mul_le_mul_of_nonneg_right hpred hpos32
      _ = ((n + 1 : ℝ) ^ 2 * p ^ j₀ * (1 - p) ^ (n - j₀)) *
            ((3 : ℝ) ^ j₀ * (n.choose j₀ : ℝ) * (2 : ℝ) ^ k) := by ring
      _ ≤ ((n + 1 : ℝ) ^ 2 * p ^ j₀ * (1 - p) ^ (n - j₀)) * (2 : ℝ) ^ n :=
          mul_le_mul_of_nonneg_left hterm_real (by positivity)
      _ = (n + 1 : ℝ) ^ 2 * p ^ j₀ * (1 - p) ^ (n - j₀) * (2 : ℝ) ^ n := by ring
  have hlog_ineq := Real.log_le_log (by positivity) Nineq1
  rw [Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity),
      Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow,
      Nat.cast_sub hj₀_le_n] at hlog_ineq
  push_cast at hlog_ineq
  have hlin := linear_entropy_identity p (n : ℝ) (j₀ : ℝ)
  have hrate := rate_mul_log_two p
  have hj₀_lb : p * (n : ℝ) - 2 ≤ (j₀ : ℝ) := by
    have hlt : p * ((n : ℝ) + 1) < (m : ℝ) + 1 := Nat.lt_floor_add_one _
    have hm_eq : (m : ℝ) = (j₀ : ℝ) + 1 := by exact_mod_cast hj₀_add.symm
    linarith
  have hj₀_diff : (p * (n : ℝ) - (j₀ : ℝ)) * (Real.log 3 - Real.log p + Real.log (1 - p)) ≤
      2 * (Real.log 3 - Real.log p + Real.log (1 - p)) := by
    exact mul_le_mul_of_nonneg_right (by linarith) hC_ent_nonneg
  have hlog_n1 : 2 * Real.log ((n : ℝ) + 1) ≤ 8 * Real.sqrt (n : ℝ) := by
    have h1 := log_le_two_sqrt ((n : ℝ) + 1) (by positivity)
    have hn1_real : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
    have h2 : Real.sqrt ((n : ℝ) + 1) ≤ 2 * Real.sqrt (n : ℝ) := by
      calc Real.sqrt ((n : ℝ) + 1)
        _ ≤ Real.sqrt (4 * (n : ℝ)) := Real.sqrt_le_sqrt (by linarith)
        _ = Real.sqrt 4 * Real.sqrt (n : ℝ) := Real.sqrt_mul (by norm_num) (n : ℝ)
        _ = 2 * Real.sqrt (n : ℝ) := by
            rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    linarith
  have hsqrt_le : Real.sqrt (n : ℝ) ≤ (n : ℝ) * (ε * Real.log 2) / K_const := by
    have hceil : (K_const / (ε * Real.log 2)) ^ 2 ≤ (n : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast (by omega : ⌈(K_const / (ε * Real.log 2)) ^ 2⌉₊ ≤ n))
    have hsqrt1 : K_const / (ε * Real.log 2) ≤ Real.sqrt (n : ℝ) := by
      rw [← Real.sqrt_sq (by positivity : 0 ≤ K_const / (ε * Real.log 2))]
      exact Real.sqrt_le_sqrt hceil
    have hmul1 : K_const * Real.sqrt (n : ℝ) ≤ Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) * (ε * Real.log 2) := by
      have := mul_le_mul_of_nonneg_right ((div_le_iff₀ (by positivity)).mp hsqrt1) (Real.sqrt_nonneg n)
      linarith
    rw [Real.mul_self_sqrt (by positivity)] at hmul1
    exact (le_div_iff₀ hK_pos).mpr (by linarith)
  have hK_bound : 2 * (Real.log 3 - Real.log p + Real.log (1 - p)) - Real.log (1 - p) +
      2 * Real.log ((n : ℝ) + 1) ≤ (n : ℝ) * ε * Real.log 2 := by
    have h1 : 1 ≤ Real.sqrt (n : ℝ) := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_le_sqrt (by exact_mod_cast (by omega : 1 ≤ n))
    have h2 : (2 * (Real.log 3 - Real.log p + Real.log (1 - p)) - Real.log (1 - p) + 8) *
        Real.sqrt (n : ℝ) ≤ (n : ℝ) * ε * Real.log 2 := by
      have := (le_div_iff₀ hK_pos).mp hsqrt_le
      linarith
    have hlog1p : Real.log (1 - p) < 0 := Real.log_neg h1p (by linarith)
    nlinarith
  have hk_log : (k : ℝ) * Real.log 2 ≤
      (n : ℝ) * (1 - p * Real.logb 2 3 - binEntropy2 p + ε) * Real.log 2 := by
    nlinarith
  have hk_le : (k : ℝ) ≤ (n : ℝ) * (1 - p * Real.logb 2 3 - binEntropy2 p + ε) :=
    le_of_mul_le_mul_right hk_log hlog2
  exact (div_le_iff₀ hn_pos).mpr (by linarith)
