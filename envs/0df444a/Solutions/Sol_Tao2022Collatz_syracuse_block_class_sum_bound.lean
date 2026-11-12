-- Prove2me | solution 1 for Tao2022Collatz.syracuse_block_class_sum_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-12T01:24:52.160739+00:00
-- url     : https://prove2.me/submissions/c553bf16-f888-4daf-a9b9-035a646fc5e7

import Mathlib
import Definitions.Def_weightedLogMassReal
import Definitions.Def_syracuseOrbitMin
set_option autoImplicit false
namespace Tao31
/-- `a n = ν₂(3n+1)`, the exponent removed by one Syracuse step. -/
noncomputable def a (n : ℕ) : ℕ := (3 * n + 1).factorization 2

lemma two_pow_a_mul_step (n : ℕ) : 2 ^ a n * syracuseStep n = 3 * n + 1 := by
  unfold a syracuseStep
  exact Nat.ordProj_mul_ordCompl_eq_self (3 * n + 1) 2

/-- Partial sums `a_1 + ... + a_k` of the n-Syracuse valuation of `n`. -/
noncomputable def A (n : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => A n k + a (syracuseStep^[k] n)

/-- The offset `Σ_{i<k} 3^{k-1-i} 2^{A_i}`, defined recursively. -/
noncomputable def S (n : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => 3 * S n k + 2 ^ A n k

/-- Affine iterate formula: `2^{a_1+...+a_k} Syr^k(n) = 3^k n + S_k(n)`. -/
lemma iterate_formula (n : ℕ) (k : ℕ) :
    2 ^ A n k * syracuseStep^[k] n = 3 ^ k * n + S n k := by
  induction k with
  | zero => simp [A, S]
  | succ k ih =>
    have h := two_pow_a_mul_step (syracuseStep^[k] n)
    rw [Function.iterate_succ_apply', A, S, pow_add]
    calc 2 ^ A n k * 2 ^ a (syracuseStep^[k] n) * syracuseStep (syracuseStep^[k] n)
        = 2 ^ A n k * (3 * syracuseStep^[k] n + 1) := by rw [mul_assoc, h]
      _ = 3 * (2 ^ A n k * syracuseStep^[k] n) + 2 ^ A n k := by ring
      _ = 3 ^ (k + 1) * n + (3 * S n k + 2 ^ A n k) := by rw [ih]; ring

/-- The first `n` Syracuse valuations `a⃗^{(n)}(N)` as a tuple. -/
noncomputable def vecn (n N : ℕ) : Fin n → ℕ := fun i => a (syracuseStep^[(i : ℕ)] N)

/-- `|a⃗| = a_1 + ... + a_n`. -/
def absv {n : ℕ} (v : Fin n → ℕ) : ℕ := ∑ i, v i


/-! ## S13: DECOMPOSE item 6a (Tao (1.19), Section 5 start): deterministic orbit bounds. -/
section Item6a
/-- `2 S_k + 2^{A_k} ≤ 3^k 2^{A_k}` (so `S_k ≤ 3^k 2^{A_k} / 2`, Tao (1.13)-style). -/
lemma two_S_add_le (N k : ℕ) : 2 * S N k + 2 ^ A N k ≤ 3 ^ k * 2 ^ A N k := by
  induction k with
  | zero => simp [S, A]
  | succ k ih =>
    have h2 : 1 ≤ 2 ^ a (syracuseStep^[k] N) := Nat.one_le_two_pow
    rw [S, A, pow_add, pow_succ]
    have e : 3 ^ k * 3 * (2 ^ A N k * 2 ^ a (syracuseStep^[k] N)) =
        3 * (3 ^ k * 2 ^ A N k) * 2 ^ a (syracuseStep^[k] N) := by ring
    rw [e]
    have h3 : 3 * (3 ^ k * 2 ^ A N k) * 2 ^ a (syracuseStep^[k] N) ≥
        3 * (2 * S N k + 2 ^ A N k) * 2 ^ a (syracuseStep^[k] N) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ ih)
    have h4 : 3 * (2 * S N k + 2 ^ A N k) * 2 ^ a (syracuseStep^[k] N) ≥
        6 * S N k + 2 * 2 ^ A N k + 2 ^ A N k * 2 ^ a (syracuseStep^[k] N) := by
      (first | linarith [Nat.zero_le (S N k), Nat.zero_le (2 ^ A N k)] | nlinarith [Nat.zero_le (S N k), Nat.zero_le (2 ^ A N k)])
    linarith

/-- `|a⃗^{(n)}(N)| = a_{[1,n]}(N)`. -/
lemma absv_vecn (n N : ℕ) : absv (vecn n N) = A N n := by
  unfold absv vecn
  rw [Fin.sum_univ_eq_sum_range (fun i => a (syracuseStep^[i] N)) n]
  induction n with
  | zero => simp [A]
  | succ n ih => rw [Finset.sum_range_succ, ih, A]

end Item6a
/-- `T_x(N) < ∞`: the orbit of `N` reaches `x` or below. -/
def Reaches (x : ℝ) (N : ℕ) : Prop := ∃ n, (syracuseStep^[n] N : ℝ) ≤ x
section Item6a3
end Item6a3
section Item6b
open Classical
end Item6b
section Item6c
open Classical in
noncomputable def T (x : ℝ) (N : ℕ) : ℕ := if h : Reaches x N then Nat.find h else 0

end Item6c
section Item6c3
end Item6c3
section Item6d
/-- Tao (5.25) for `q`-separated sets: `Σ_{M ∈ S} 1/M ≤ 1/M0 + log(M1/M0)/q` when `S ⊂ [M0, M1]`
and distinct elements of `S` are at least `q ≤ M0` apart. -/
lemma sep_harm (q M0 : ℕ) (hq : 1 ≤ q) (hqM : q ≤ M0) (S : Finset ℕ) :
    (∀ M ∈ S, ∀ M' ∈ S, M < M' → M + q ≤ M') → ∀ M1 : ℕ, M0 ≤ M1 →
      (∀ M ∈ S, M0 ≤ M ∧ M ≤ M1) →
      ∑ M ∈ S, (1 : ℝ) / M ≤ 1 / M0 + Real.log ((M1 : ℝ) / M0) / q := by
  have hM0 : (0 : ℝ) < M0 := by exact_mod_cast (show 0 < M0 by omega)
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hlog0 : ∀ M1 : ℕ, M0 ≤ M1 → 0 ≤ Real.log ((M1 : ℝ) / M0) / q := by
    intro M1 hM1
    apply div_nonneg _ hq0.le
    apply Real.log_nonneg
    rw [le_div_iff₀ hM0, one_mul]; exact_mod_cast hM1
  induction S using Finset.induction_on_max with
  | empty =>
    intro _ M1 hM1 _
    have := hlog0 M1 hM1
    have : (0 : ℝ) ≤ 1 / M0 := by positivity
    simp only [Finset.sum_empty]; linarith
  | insert a s hlt ih =>
    intro hsep M1 hM1 hbd
    have ha := hbd a (Finset.mem_insert_self a s)
    rw [Finset.sum_insert (fun h => lt_irrefl a (hlt a h))]
    have hsep' : ∀ M ∈ s, ∀ M' ∈ s, M < M' → M + q ≤ M' := fun M hM M' hM' h =>
      hsep M (Finset.mem_insert_of_mem hM) M' (Finset.mem_insert_of_mem hM') h
    have ha_pos : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by omega)
    have haM1 : (a : ℝ) ≤ M1 := by exact_mod_cast ha.2
    rcases s.eq_empty_or_nonempty with hs | ⟨x, hx⟩
    · subst hs
      simp only [Finset.sum_empty, add_zero]
      have h1 : (1 : ℝ) / a ≤ 1 / M0 := one_div_le_one_div_of_le hM0 (by exact_mod_cast ha.1)
      have := hlog0 M1 hM1
      linarith
    · have hxa : x + q ≤ a :=
        hsep x (Finset.mem_insert_of_mem hx) a (Finset.mem_insert_self a s) (hlt x hx)
      have hxM0 := (hbd x (Finset.mem_insert_of_mem hx)).1
      have hbd' : ∀ M ∈ s, M0 ≤ M ∧ M ≤ a - q := fun M hM =>
        ⟨(hbd M (Finset.mem_insert_of_mem hM)).1, by
          have := hsep M (Finset.mem_insert_of_mem hM) a (Finset.mem_insert_self a s) (hlt M hM)
          omega⟩
      have ih' := ih hsep' (a - q) (by omega) hbd'
      have hcast : ((a - q : ℕ) : ℝ) = (a : ℝ) - q := Nat.cast_sub (by omega)
      rw [hcast] at ih'
      have haq : (0 : ℝ) < (a : ℝ) - q := by
        have h : (M0 : ℝ) ≤ ((a - q : ℕ) : ℝ) := by exact_mod_cast (show M0 ≤ a - q by omega)
        rw [hcast] at h; linarith
      have hkey : (1 : ℝ) / a ≤ (Real.log ((a : ℝ) / M0) - Real.log (((a : ℝ) - q) / M0)) / q := by
        rw [← Real.log_div (div_pos ha_pos hM0).ne' (div_pos haq hM0).ne']
        have e : (a : ℝ) / M0 / (((a : ℝ) - q) / M0) = a / ((a : ℝ) - q) := by
          field_simp
        rw [e, le_div_iff₀ hq0]
        have h := Real.one_sub_inv_le_log_of_pos (div_pos ha_pos haq)
        rw [inv_div] at h
        have e2 : 1 - ((a : ℝ) - q) / a = q / a := by
          rw [sub_div, div_self ha_pos.ne']; ring
        rw [e2] at h
        calc 1 / (a : ℝ) * q = q / a := by ring
          _ ≤ _ := h
      have hmono : Real.log ((a : ℝ) / M0) ≤ Real.log ((M1 : ℝ) / M0) :=
        Real.log_le_log (div_pos ha_pos hM0) (div_le_div_of_nonneg_right haM1 hM0.le)
      have h3 : Real.log ((a : ℝ) / M0) / q ≤ Real.log ((M1 : ℝ) / M0) / q :=
        div_le_div_of_nonneg_right hmono hq0.le
      have e3 : (Real.log ((a : ℝ) / M0) - Real.log (((a : ℝ) - q) / M0)) / q =
          Real.log ((a : ℝ) / M0) / q - Real.log (((a : ℝ) - q) / M0) / q := sub_div _ _ _
      linarith

end Item6d
section Item6d2
/-- `A` and `S` up to `k` depend only on the first `k` valuations. -/
lemma AS_congr (N N' : ℕ) : ∀ k, (∀ i < k, a (syracuseStep^[i] N) = a (syracuseStep^[i] N')) →
    A N k = A N' k ∧ S N k = S N' k := by
  intro k
  induction k with
  | zero => intro _; exact ⟨rfl, rfl⟩
  | succ k ih =>
    intro h
    obtain ⟨hA, hS⟩ := ih (fun i hi => h i (by omega))
    have e1 : A N (k + 1) = A N k + a (syracuseStep^[k] N) := rfl
    have e2 : A N' (k + 1) = A N' k + a (syracuseStep^[k] N') := rfl
    have e3 : S N (k + 1) = 3 * S N k + 2 ^ A N k := rfl
    have e4 : S N' (k + 1) = 3 * S N' k + 2 ^ A N' k := rfl
    rw [e1, e2, e3, e4, hA, hS, h k (by omega)]
    exact ⟨rfl, rfl⟩

lemma step_odd' (n : ℕ) : Odd (syracuseStep n) := by
  have h := Nat.coprime_ordCompl Nat.prime_two (show 3 * n + 1 ≠ 0 by omega)
  unfold syracuseStep
  exact Nat.coprime_two_left.1 h

lemma iter_odd (N k : ℕ) (hk : 1 ≤ k) : Odd (syracuseStep^[k] N) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [Function.iterate_succ_apply']
  exact step_odd' _

/-- Lemma 5.3 ingredient (Tao (1.7)): equal first `k ≥ 1` valuations force `N ≡ N' (mod 2^{a_{[1,k]}+1})`. -/
lemma two_pow_dvd_of_prefix (N N' k : ℕ) (hk : 1 ≤ k)
    (h : ∀ i < k, a (syracuseStep^[i] N) = a (syracuseStep^[i] N')) :
    (2 : ℤ) ^ (A N k + 1) ∣ (N' : ℤ) - N := by
  obtain ⟨hA, hS⟩ := AS_congr N N' k h
  have f := iterate_formula N k
  have f' := iterate_formula N' k
  rw [← hA, ← hS] at f'
  obtain ⟨u, hu⟩ := iter_odd N k hk
  obtain ⟨u', hu'⟩ := iter_odd N' k hk
  have f1 : ((2 ^ A N k * syracuseStep^[k] N : ℕ) : ℤ) = ((3 ^ k * N + S N k : ℕ) : ℤ) := by rw [f]
  have f2 : ((2 ^ A N k * syracuseStep^[k] N' : ℕ) : ℤ) = ((3 ^ k * N' + S N k : ℕ) : ℤ) := by rw [f']
  rw [hu] at f1; rw [hu'] at f2
  push_cast at f1 f2
  have e : (3 : ℤ) ^ k * ((N' : ℤ) - N) = 2 ^ (A N k + 1) * ((u' : ℤ) - u) := by
    rw [pow_succ]; linear_combination f1 - f2
  have hcop : IsCoprime ((2 : ℤ) ^ (A N k + 1)) ((3 : ℤ) ^ k) :=
    IsCoprime.pow ⟨-1, 1, by norm_num⟩
  have hd : (2 : ℤ) ^ (A N k + 1) ∣ (3 : ℤ) ^ k * ((N' : ℤ) - N) := ⟨(u' : ℤ) - u, e⟩
  first
    | exact hcop.dvd_of_dvd_mul_left hd
    | exact hcop.dvd_of_dvd_mul_right hd
    | exact (hcop.dvd_mul_left).1 hd
    | exact (hcop.dvd_mul_right).1 hd

/-- CRT separation: numbers congruent mod `2^e` and mod `3^k` are `2^e 3^k`-separated. -/
lemma sep_of_dvd (M M' e k : ℕ) (h2 : (2 : ℤ) ^ e ∣ (M' : ℤ) - M) (h3 : (3 : ℤ) ^ k ∣ (M' : ℤ) - M)
    (hlt : M < M') : M + 2 ^ e * 3 ^ k ≤ M' := by
  have hcop : IsCoprime ((2 : ℤ) ^ e) ((3 : ℤ) ^ k) := IsCoprime.pow ⟨-1, 1, by norm_num⟩
  have hd := hcop.mul_dvd h2 h3
  have hpos : (0 : ℤ) < (M' : ℤ) - M := by
    have : (M : ℤ) < M' := by exact_mod_cast hlt
    linarith
  have hle := Int.le_of_dvd hpos hd
  have : ((M + 2 ^ e * 3 ^ k : ℕ) : ℤ) ≤ (M' : ℤ) := by push_cast; linarith
  exact_mod_cast this

end Item6d2
section Item6d3
open Classical
/-- Upper bound from `Syr^m M ≤ x` (Tao (5.24), right half). -/
lemma M_upper (x : ℝ) (M m : ℕ) (h : (syracuseStep^[m] M : ℝ) ≤ x) :
    (3 : ℝ) ^ m * M ≤ 2 ^ A M m * x := by
  have f := iterate_formula M m
  have f' : (2 : ℝ) ^ A M m * (syracuseStep^[m] M : ℝ) = 3 ^ m * M + S M m := by exact_mod_cast f
  have hS : (0 : ℝ) ≤ S M m := Nat.cast_nonneg _
  have h2 : (0 : ℝ) ≤ 2 ^ A M m := by positivity
  have h3 := mul_le_mul_of_nonneg_left h h2
  linarith

/-- Lower bound from `x < Syr^j M` (Tao (5.24), left half), when `3^j ≤ x`. -/
lemma M_lower (x : ℝ) (M j : ℕ) (h3 : (3 : ℝ) ^ j ≤ x) (h : x < (syracuseStep^[j] M : ℝ)) :
    (2 : ℝ) ^ A M j * x < 2 * 3 ^ j * M := by
  have f := iterate_formula M j
  have f' : (2 : ℝ) ^ A M j * (syracuseStep^[j] M : ℝ) = 3 ^ j * M + S M j := by exact_mod_cast f
  have hS := two_S_add_le M j
  have hS' : 2 * (S M j : ℝ) + 2 ^ A M j ≤ 3 ^ j * 2 ^ A M j := by exact_mod_cast hS
  have h2 : (0 : ℝ) < 2 ^ A M j := by positivity
  have h4 : (2 : ℝ) ^ A M j * x < 2 ^ A M j * (syracuseStep^[j] M : ℝ) := mul_lt_mul_of_pos_left h h2
  have h5 : (3 : ℝ) ^ j * 2 ^ A M j ≤ x * 2 ^ A M j := mul_le_mul_of_nonneg_right h3 h2.le
  linarith

/-- Lemma 5.3, one valuation block `b = a⃗^{(m)}(M)`: the class sum is `≤ 2^{-|b|}(2 + b_m)`. -/
lemma cb_bound (x : ℝ) (hx : 0 < x) (m k : ℕ) (hm : 1 ≤ m) (b : Fin m → ℕ) (S : Finset ℕ)
    (hsize : 4 * (3 : ℝ) ^ (k + m) * 2 ^ (b ⟨m - 1, by omega⟩) ≤ x)
    (hS : ∀ M ∈ S, vecn m M = b ∧ (syracuseStep^[m] M : ℝ) ≤ x ∧ x < (syracuseStep^[m - 1] M : ℝ))
    (hcong : ∀ M ∈ S, ∀ M' ∈ S, (3 : ℤ) ^ k ∣ (M' : ℤ) - M) :
    (3 : ℝ) ^ k * ∑ M ∈ S, (1 : ℝ) / M ≤ ((1 : ℝ) / 2) ^ absv b * (2 + b ⟨m - 1, by omega⟩) := by
  rcases S.eq_empty_or_nonempty with hSe | ⟨M₀, hM₀⟩
  · rw [hSe, Finset.sum_empty, mul_zero]; positivity
  set a0 := b ⟨m - 1, by omega⟩ with ha0
  set Ab := absv b with hAb
  have hAm : ∀ M ∈ S, A M m = Ab := fun M hM => by rw [hAb, ← (hS M hM).1, absv_vecn]
  have hA1 : ∀ M ∈ S, A M (m - 1) + a0 = Ab := by
    intro M hM
    have e := (show A M ((m - 1) + 1) = A M (m - 1) + a (syracuseStep^[m - 1] M) from rfl)
    rw [Nat.sub_add_cancel hm] at e
    have e2 : a (syracuseStep^[m - 1] M) = a0 := by
      rw [ha0, ← (hS M hM).1]; rfl
    rw [← hAm M hM, e, e2]
  have hab : a0 ≤ Ab := by have := hA1 M₀ hM₀; omega
  set P : ℝ := (2 : ℝ) ^ (Ab - a0) with hP
  set T : ℝ := (3 : ℝ) ^ (m - 1) with hT
  set G : ℝ := (3 : ℝ) ^ k with hG
  have hPpos : 0 < P := by positivity
  have hTpos : 0 < T := by positivity
  have hGpos : 0 < G := by positivity
  have h2a : (0 : ℝ) < 2 ^ a0 := by positivity
  have hG1 : (1 : ℝ) ≤ G := one_le_pow₀ (by norm_num)
  have h2a1 : (1 : ℝ) ≤ 2 ^ a0 := one_le_pow₀ (by norm_num)
  have h2Ab : (2 : ℝ) ^ Ab = P * 2 ^ a0 := by rw [hP, ← pow_add, Nat.sub_add_cancel hab]
  have h3m : (3 : ℝ) ^ m = 3 * T := by
    rw [hT, ← pow_succ']; congr 1; omega
  have h3km : (3 : ℝ) ^ (k + m) = G * (3 * T) := by rw [pow_add, h3m]
  rw [h3km] at hsize
  have hGT : 0 ≤ G * T * 2 ^ a0 := by positivity
  have hx2 : 4 * G * T * 2 ^ a0 ≤ x := by (first | linarith | nlinarith)
  have hTx : T ≤ x := by
    have e1 : T ≤ G * T := le_mul_of_one_le_left hTpos.le hG1
    have e2 : G * T ≤ G * T * 2 ^ a0 := le_mul_of_one_le_right (by positivity) h2a1
    linarith
  set L : ℝ := P * x / (2 * T) with hL
  set U : ℝ := P * 2 ^ a0 * x / (3 * T) with hU
  have hLpos : 0 < L := by positivity
  have hlow : ∀ M ∈ S, L < M := by
    intro M hM
    have h := M_lower x M (m - 1) hTx (hS M hM).2.2
    have e : A M (m - 1) = Ab - a0 := by have := hA1 M hM; omega
    rw [e] at h
    rw [hL, div_lt_iff₀ (by positivity)]; linarith
  have hup : ∀ M ∈ S, (M : ℝ) ≤ U := by
    intro M hM
    have h := M_upper x M m (hS M hM).2.1
    rw [hAm M hM, h2Ab, h3m] at h
    rw [hU, le_div_iff₀ (by positivity)]; linarith
  set q : ℕ := 2 ^ (Ab + 1) * 3 ^ k with hq
  have hqR : (q : ℝ) = 2 * (P * 2 ^ a0) * G := by
    rw [hq]; push_cast; rw [pow_succ, h2Ab]; ring
  have hsep : ∀ M ∈ S, ∀ M' ∈ S, M < M' → M + q ≤ M' := by
    intro M hM M' hM' hlt
    have hpre : ∀ i < m, a (syracuseStep^[i] M) = a (syracuseStep^[i] M') := by
      intro i hi
      have := congrFun ((hS M hM).1.trans (hS M' hM').1.symm) ⟨i, hi⟩
      simpa [vecn] using this
    have h2 := two_pow_dvd_of_prefix M M' m hm hpre
    rw [hAm M hM] at h2
    exact sep_of_dvd M M' (Ab + 1) k h2 (hcong M hM M' hM') hlt
  have hqL : (q : ℝ) ≤ L := by
    rw [hqR, hL, le_div_iff₀ (by positivity)]
    have := mul_le_mul_of_nonneg_left hx2 hPpos.le
    (first | linarith | nlinarith)
  set M0 : ℕ := ⌈L⌉₊ with hM0
  set M1 : ℕ := ⌊U⌋₊ with hM1
  have hM0L : L ≤ (M0 : ℝ) := Nat.le_ceil L
  have hq1 : 1 ≤ q := by have : 0 < q := by positivity
                         omega
  have hqM0 : q ≤ M0 := by
    have : (q : ℝ) ≤ (M0 : ℝ) := le_trans hqL hM0L
    exact_mod_cast this
  have hrange : ∀ M ∈ S, M0 ≤ M ∧ M ≤ M1 :=
    fun M hM => ⟨Nat.ceil_le.2 (hlow M hM).le, Nat.le_floor (hup M hM)⟩
  have hM01 : M0 ≤ M1 := le_trans (hrange M₀ hM₀).1 (hrange M₀ hM₀).2
  have hsum := sep_harm q M0 hq1 hqM0 S hsep M1 hM01 hrange
  have hM0pos : (0 : ℝ) < M0 := lt_of_lt_of_le hLpos hM0L
  have hM1U : (M1 : ℝ) ≤ U := Nat.floor_le (by positivity)
  have hM10 : (M0 : ℝ) ≤ M1 := by exact_mod_cast hM01
  have hlog : Real.log ((M1 : ℝ) / M0) ≤ (a0 + 1 : ℝ) := by
    have hr : (M1 : ℝ) / M0 ≤ 2 ^ (a0 + 1) := by
      rw [div_le_iff₀ hM0pos]
      have hUL : U = 2 * 2 ^ a0 / 3 * L := by
        rw [hU, hL]; field_simp
      calc (M1 : ℝ) ≤ U := hM1U
        _ = 2 * 2 ^ a0 / 3 * L := hUL
        _ ≤ 2 ^ (a0 + 1) * M0 := by
          rw [pow_succ]
          have := mul_le_mul_of_nonneg_left hM0L (show (0 : ℝ) ≤ 2 ^ a0 * 2 by positivity)
          (first | linarith | nlinarith)
    have hpos : (0 : ℝ) < (M1 : ℝ) / M0 := div_pos (lt_of_lt_of_le hM0pos hM10) hM0pos
    calc Real.log ((M1 : ℝ) / M0) ≤ Real.log (2 ^ (a0 + 1)) := Real.log_le_log hpos hr
      _ = (a0 + 1 : ℝ) * Real.log 2 := by rw [Real.log_pow]; push_cast; ring
      _ ≤ (a0 + 1 : ℝ) :=
        mul_le_of_le_one_right (by positivity) (by linarith [Real.log_two_lt_d9])
  have hR : ((1 : ℝ) / 2) ^ Ab = 1 / (P * 2 ^ a0) := by rw [one_div_pow, h2Ab]
  have p1 : G * (1 / (M0 : ℝ)) ≤ 1 / (P * 2 ^ a0) := by
    have e1 : G * (1 / (M0 : ℝ)) ≤ G * (1 / L) :=
      mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le hLpos hM0L) hGpos.le
    have e2 : G * (1 / L) ≤ 1 / (P * 2 ^ a0) := by
      rw [hL, mul_one_div, div_div_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
      have := mul_le_mul_of_nonneg_left hx2 hPpos.le
      have hm4 : 0 ≤ P * G * T * 2 ^ a0 := by positivity
      linarith
    linarith
  have p2 : G * (Real.log ((M1 : ℝ) / M0) / q) ≤ (a0 + 1) / 2 * (1 / (P * 2 ^ a0)) := by
    rw [hqR]
    have e : G * (Real.log ((M1 : ℝ) / M0) / (2 * (P * 2 ^ a0) * G)) =
        Real.log ((M1 : ℝ) / M0) / (2 * (P * 2 ^ a0)) := by
      field_simp
    rw [e, div_le_iff₀ (by positivity)]
    have : (a0 + 1) / 2 * (1 / (P * 2 ^ a0)) * (2 * (P * 2 ^ a0)) = (a0 + 1 : ℝ) := by
      field_simp
    rw [this]; exact hlog
  calc G * ∑ M ∈ S, (1 : ℝ) / M ≤ G * (1 / (M0 : ℝ) + Real.log ((M1 : ℝ) / M0) / q) :=
        mul_le_mul_of_nonneg_left hsum hGpos.le
    _ = G * (1 / (M0 : ℝ)) + G * (Real.log ((M1 : ℝ) / M0) / q) := by ring
    _ ≤ 1 / (P * 2 ^ a0) + (a0 + 1) / 2 * (1 / (P * 2 ^ a0)) := add_le_add p1 p2
    _ ≤ ((1 : ℝ) / 2) ^ Ab * (2 + a0) := by
        rw [hR]
        have hr0 : (0 : ℝ) ≤ 1 / (P * 2 ^ a0) := by positivity
        have ha0' : (0 : ℝ) ≤ a0 := by positivity
        have := mul_nonneg hr0 ha0'
        linarith

end Item6d3
section ZAsymp
end ZAsymp
section Item6e1
open Classical
end Item6e1
section Item6e2
open Classical
end Item6e2
section Item6e3
open Classical
end Item6e3
section Item6e4
open Classical
end Item6e4
section Item6e5
open Classical
end Item6e5
section Item6f2
open Classical
end Item6f2
section Item6f3
open Classical
end Item6f3
section Item6f4
open Classical
end Item6f4
section Item6f5
open Classical
end Item6f5
section Num120
end Num120
section P120
open Classical
end P120
section P111
open Classical
end P111
set_option autoImplicit false
set_option autoImplicit false
set_option autoImplicit false
section Four
open Finset
end Four
section Fact
open Finset
open Classical
end Fact
section Fsq
open Finset
open Classical
end Fsq
section Red7h
open Finset
open Classical
end Red7h
section Tele
open Finset
open Classical
end Tele
section Chain
open Finset
open Classical
end Chain
section Asm7g
open Finset
open Classical
end Asm7g
section Dev7g
open Finset
open Classical
end Dev7g
section Dec7g
open Finset
open Classical
end Dec7g
section Bad7g
open Finset
open Classical
end Bad7g
section Core7g
open Finset
open Classical
end Core7g
section IF114
open Classical
end IF114
section IF111
end IF111
section C4
open Classical
end C4

end Tao31

open Tao31 in
theorem solution :
    ∀ (x : ℝ) (hx : 0 < x) (m k : ℕ) (hm : 1 ≤ m) (b : Fin m → ℕ) (S : Finset ℕ) (hsize : 4 * (3 : ℝ) ^ (k + m) * 2 ^ (b ⟨m - 1, by omega⟩) ≤ x) (hS : ∀ M ∈ S, (fun i : Fin m => (3 * syracuseStep^[(i : ℕ)] M + 1).factorization 2) = b ∧ (syracuseStep^[m] M : ℝ) ≤ x ∧ x < (syracuseStep^[m - 1] M : ℝ)) (hcong : ∀ M ∈ S, ∀ M' ∈ S, (3 : ℤ) ^ k ∣ (M' : ℤ) - M),
    (3 : ℝ) ^ k * ∑ M ∈ S, (1 : ℝ) / M ≤ ((1 : ℝ) / 2) ^ (∑ i, b i) * (2 + b ⟨m - 1, by omega⟩) := by
  intro x hx m k hm b S hsize hS hcong
  exact Tao31.cb_bound x hx m k hm b S hsize hS hcong
