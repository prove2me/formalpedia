-- Prove2me | solution 1 for Tao2022Collatz.first_passage_stabilisation_of_mixing
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-12T01:34:25.365928+00:00
-- url     : https://prove2.me/submissions/5acd2b3e-0291-433f-a8d5-d2de94c6fcac

import Mathlib
import Definitions.Def_weightedLogMassReal
import Definitions.Def_syracuseOrbitMin

set_option autoImplicit false

/-! Tao, Almost all Collatz orbits attain almost bounded values (arXiv:1909.03562v7).
Foundational layer for Theorem 3.1: the n-Syracuse valuation, the affine iterate formula
(Tao (1.5)/(1.7)) and the orbit-minimum facts used in Section 3. -/

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

lemma S_eq_sum (n : ℕ) (k : ℕ) :
    S n k = ∑ i ∈ Finset.range k, 3 ^ (k - 1 - i) * 2 ^ A n i := by
  induction k with
  | zero => simp [S]
  | succ k ih =>
    rw [S, ih, Finset.sum_range_succ, Finset.mul_sum]
    congr 1
    · apply Finset.sum_congr rfl
      intro i hi
      have hi' : i < k := Finset.mem_range.mp hi
      have : k + 1 - 1 - i = (k - 1 - i) + 1 := by omega
      rw [this, pow_succ]; ring
    · simp

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

/-- Orbit upper bound: `Syr^k N ≤ 3^k N / 2^{A_k} + 3^k` (Tao (1.7), (1.13)). -/
lemma iter_le (N k : ℕ) :
    (syracuseStep^[k] N : ℝ) ≤ 3 ^ k * N / 2 ^ A N k + 3 ^ k := by
  have h1 := iterate_formula N k
  have h2 := two_S_add_le N k
  have hp : (0 : ℝ) < 2 ^ A N k := by positivity
  have h1' : (2 : ℝ) ^ A N k * (syracuseStep^[k] N : ℝ) = 3 ^ k * N + S N k := by
    exact_mod_cast h1
  have h2' : (2 : ℝ) * S N k + 2 ^ A N k ≤ 3 ^ k * 2 ^ A N k := by exact_mod_cast h2
  have hS : (S N k : ℝ) ≤ 3 ^ k * 2 ^ A N k := by
    have : (0 : ℝ) ≤ 2 ^ A N k := hp.le
    (first | linarith [(Nat.cast_nonneg (S N k) : (0 : ℝ) ≤ S N k)] | nlinarith [(Nat.cast_nonneg (S N k) : (0 : ℝ) ≤ S N k)])
  have key : (syracuseStep^[k] N : ℝ) = (3 ^ k * N + S N k) / 2 ^ A N k := by
    field_simp; linarith
  rw [key, add_div]
  have : (S N k : ℝ) / 2 ^ A N k ≤ 3 ^ k := by rw [div_le_iff₀ hp]; linarith
  linarith

/-- `|a⃗^{(n)}(N)| = a_{[1,n]}(N)`. -/
lemma absv_vecn (n N : ℕ) : absv (vecn n N) = A N n := by
  unfold absv vecn
  rw [Fin.sum_univ_eq_sum_range (fun i => a (syracuseStep^[i] N)) n]
  induction n with
  | zero => simp [A]
  | succ n ih => rw [Finset.sum_range_succ, ih, A]

lemma key_nat (n : ℕ) (hn : 5 ≤ n) : 1024 * (3 ^ (10 * n) * 2 ^ n) ≤ 2 ^ (19 * n) := by
  have e1 : 3 ^ (10 * n) * 2 ^ n = 118098 ^ n := by
    rw [pow_mul, ← mul_pow]; norm_num
  have e2 : 2 ^ (19 * n) = 524288 ^ n := by rw [pow_mul]; norm_num
  rw [e1, e2]
  clear e1 e2
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ m _ ih =>
    rw [pow_succ, pow_succ]
    calc 1024 * (118098 ^ m * 118098) = (1024 * 118098 ^ m) * 118098 := by ring
      _ ≤ 524288 ^ m * 118098 := Nat.mul_le_mul_right _ ih
      _ ≤ 524288 ^ m * 524288 := Nat.mul_le_mul_left _ (by norm_num)

/-- Tao (5.5) deterministic half: if `|a⃗^{(n)}(N)| ≥ 1.9 n`, `2^{10n} ≤ x` and `N ≤ x · 2^{n/10}`,
then `Syr^n N ≤ x` (so `T_x(N) ≤ n`). -/
lemma reach_core (x : ℝ) (n N : ℕ) (hn : 5 ≤ n) (hx : (2 : ℝ) ^ (10 * n) ≤ x)
    (hN : (N : ℝ) ^ 10 ≤ x ^ 10 * 2 ^ n) (hA : 19 * n ≤ 10 * A N n) :
    (syracuseStep^[n] N : ℝ) ≤ x := by
  have h := iter_le N n
  have hx0 : 0 ≤ x := le_trans (by positivity) hx
  have hp : (0 : ℝ) < 2 ^ A N n := by positivity
  set t : ℝ := 3 ^ n * N / 2 ^ A N n with ht
  have ht0 : 0 ≤ t := by positivity
  have hk : (1024 : ℝ) * (3 ^ (10 * n) * 2 ^ n) ≤ 2 ^ (19 * n) := by exact_mod_cast key_nat n hn
  have h19 : (2 : ℝ) ^ (19 * n) ≤ (2 ^ A N n) ^ 10 := by
    rw [← pow_mul]; exact pow_le_pow_right₀ (by norm_num) (by omega)
  have ht10 : t ^ 10 * (2 ^ A N n) ^ 10 = 3 ^ (10 * n) * (N : ℝ) ^ 10 := by
    rw [ht, div_pow, div_mul_cancel₀ _ (by positivity), mul_pow, ← pow_mul, mul_comm n 10]
  clear_value t
  have hT : t ^ 10 ≤ (x / 2) ^ 10 := by
    have e : (x / 2) ^ 10 = x ^ 10 / 1024 := by ring
    rw [e, le_div_iff₀ (by norm_num)]
    have hP : (0 : ℝ) < (2 ^ A N n) ^ 10 := by positivity
    have hx10 : (0 : ℝ) ≤ x ^ 10 := by positivity
    have hA' : t ^ 10 * 1024 * (2 ^ A N n) ^ 10 ≤ x ^ 10 * (2 ^ A N n) ^ 10 := by
      calc t ^ 10 * 1024 * (2 ^ A N n) ^ 10 = 1024 * (3 ^ (10 * n) * (N : ℝ) ^ 10) := by
            rw [← ht10]; ring
        _ ≤ 1024 * (3 ^ (10 * n) * (x ^ 10 * 2 ^ n)) := by gcongr
        _ = x ^ 10 * (1024 * (3 ^ (10 * n) * 2 ^ n)) := by ring
        _ ≤ x ^ 10 * 2 ^ (19 * n) := by gcongr
        _ ≤ x ^ 10 * (2 ^ A N n) ^ 10 := by gcongr
    exact le_of_mul_le_mul_right hA' hP
  have ht2 : t ≤ x / 2 := (pow_le_pow_iff_left₀ ht0 (by positivity) (by norm_num)).1 hT
  have h3 : (3 : ℝ) ^ n ≤ x / 2 := by
    have : (2 : ℝ) * 3 ^ n ≤ 2 ^ (10 * n) := by
      have hn1 : 1 ≤ n := by omega
      have : (2 : ℕ) * 3 ^ n ≤ 2 ^ (10 * n) := by
        calc 2 * 3 ^ n ≤ 2 ^ n * 3 ^ n := Nat.mul_le_mul_right _ (Nat.le_self_pow (by omega) 2)
          _ = 6 ^ n := (mul_pow 2 3 n).symm
          _ ≤ 1024 ^ n := Nat.pow_le_pow_left (by norm_num) n
          _ = 2 ^ (10 * n) := by rw [pow_mul]; norm_num
      exact_mod_cast this
    linarith
  linarith

end Item6a
/-- Tuples with entries in `[1, 3n]`. -/
noncomputable def Bset (n : ℕ) : Finset (Fin n → ℕ) :=
  Fintype.piFinset (fun _ => Finset.Icc 1 (3 * n))

/-- Tuples `a⃗ ∈ (ℕ+1)^n` with `|a⃗| < 3n` (Tao's `|a⃗| < n'`, `n' = 3n`). -/
noncomputable def Tset (n : ℕ) : Finset (Fin n → ℕ) := (Bset n).filter (fun v => absv v < 3 * n)
/-- Tuples `a ∈ [1,K]^n` (Geom(2)^n truncated at `K`; weight `2^{-|a|}`). -/
noncomputable def Box (n K : ℕ) : Finset (Fin n → ℕ) := Fintype.piFinset (fun _ => Finset.Icc 1 K)
/-- Tao's `α = 1.001` (1.18). -/
noncomputable def alph : ℝ := 1001 / 1000

open Classical in
/-- Odd integers in `[y, y^α]`, the support of `N_y`. -/
noncomputable def oddIcc (y : ℝ) : Finset ℕ := (Finset.Icc ⌈y⌉₊ ⌊y ^ alph⌋₊).filter Odd

/-- Normaliser of the log-uniform weight `1/N` on `oddIcc y`. -/
noncomputable def Z (y : ℝ) : ℝ := ∑ N ∈ oddIcc y, (1 : ℝ) / N

open Classical in
/-- `P(Q(N_y))` for the log-uniform odd variable `N_y` on `[y, y^α]`. -/
noncomputable def prob (y : ℝ) (Q : ℕ → Prop) : ℝ :=
  (∑ N ∈ oddIcc y, if Q N then (1 : ℝ) / N else 0) / Z y

/-- `T_x(N) < ∞`: the orbit of `N` reaches `x` or below. -/
def Reaches (x : ℝ) (N : ℕ) : Prop := ∃ n, (syracuseStep^[n] N : ℝ) ≤ x
lemma Z_nonneg (y : ℝ) : 0 ≤ Z y := Finset.sum_nonneg (fun N _ => by positivity)

/-- Copy of the main draft's `prob_mono` (drop when merging). -/
lemma prob_mono (y : ℝ) {P Q : ℕ → Prop} (hPQ : ∀ N, P N → Q N) : prob y P ≤ prob y Q := by
  unfold prob
  apply div_le_div_of_nonneg_right _ (Z_nonneg y)
  apply Finset.sum_le_sum; intro N _
  by_cases hP : P N
  · simp [hP, hPQ N hP]
  · by_cases hQ : Q N <;> simp [hP, hQ] <;> positivity

/-! ## S14: DECOMPOSE item 6a3 (Tao (1.19)): assembly from Prop 1.9 for `N_y` and the lower tail. -/
section Item6a3

lemma Z_ge {y : ℝ} (hy : 1 ≤ y) (h3 : 3 * y + 3 ≤ y ^ alph) : 1 / 3 ≤ Z y := by
  set c := ⌈y⌉₊ with hc
  have hc1 : 0 < c := Nat.ceil_pos.mpr (by linarith)
  have hcy : (c : ℝ) < y + 1 := Nat.ceil_lt_add_one (by linarith)
  obtain ⟨c', hc'odd, hc'1, hc'2⟩ : ∃ c', Odd c' ∧ c ≤ c' ∧ c' ≤ c + 1 := by
    rcases Nat.even_or_odd c with h | h
    · exact ⟨c + 1, h.add_one, by omega, le_refl _⟩
    · exact ⟨c, h, le_refl _, by omega⟩
  have hsub : (Finset.range c).image (fun k => c' + 2 * k) ⊆ oddIcc y := by
    intro N hN
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hN
    rw [Finset.mem_range] at hk
    unfold oddIcc
    rw [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨by omega, ?_⟩, ?_⟩
    · apply Nat.le_floor
      have : c' + 2 * k ≤ 3 * c := by omega
      have h' : ((c' + 2 * k : ℕ) : ℝ) ≤ 3 * c := by exact_mod_cast this
      linarith
    · exact hc'odd.add_even (even_two_mul k)
  have hinj : Set.InjOn (fun k => c' + 2 * k) (Finset.range c : Set ℕ) := by
    intro a _ b _ h; simp only at h; omega
  have hcpos : (0 : ℝ) < c := by exact_mod_cast hc1
  calc (1 : ℝ) / 3 ≤ ∑ k ∈ Finset.range c, (1 : ℝ) / ((c' + 2 * k : ℕ) : ℝ) := by
        have hb : ∀ k ∈ Finset.range c, (1 : ℝ) / (3 * c) ≤ 1 / ((c' + 2 * k : ℕ) : ℝ) := by
          intro k hk
          rw [Finset.mem_range] at hk
          have h1 : c' + 2 * k ≤ 3 * c := by omega
          have h2 : 1 ≤ c' + 2 * k := by omega
          have hpos : (0 : ℝ) < ((c' + 2 * k : ℕ) : ℝ) := by exact_mod_cast h2
          apply one_div_le_one_div_of_le hpos
          exact_mod_cast h1
        have := Finset.card_nsmul_le_sum _ _ _ hb
        rw [Finset.card_range, nsmul_eq_mul] at this
        calc (1 : ℝ) / 3 = c * (1 / (3 * c)) := by field_simp
          _ ≤ _ := this
    _ = ∑ N ∈ (Finset.range c).image (fun k => c' + 2 * k), (1 : ℝ) / N := by
        rw [Finset.sum_image hinj]
    _ ≤ Z y := by
        unfold Z
        exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)

lemma small_of_notReach {x y : ℝ} {n N : ℕ} (hn : 5 ≤ n) (hx : (2 : ℝ) ^ (10 * n) ≤ x)
    (hy0 : 0 ≤ y) (hy : (y ^ alph) ^ 10 ≤ x ^ 10 * 2 ^ n) (hNy : N ∈ oddIcc y)
    (hR : ¬ Reaches x N) : 10 * absv (vecn n N) < 19 * n := by
  by_contra h
  push_neg at h
  rw [absv_vecn] at h
  apply hR
  refine ⟨n, reach_core x n N hn hx ?_ h⟩
  have hN : (N : ℝ) ≤ y ^ alph := by
    unfold oddIcc at hNy
    have h1 := (Finset.mem_Icc.1 (Finset.mem_filter.1 hNy).1).2
    have h0 : 0 ≤ y ^ alph := Real.rpow_nonneg hy0 _
    exact le_trans (by exact_mod_cast h1) (Nat.floor_le h0)
  exact le_trans (pow_le_pow_left₀ (Nat.cast_nonneg _) hN 10) hy

lemma tset_tail (n : ℕ) (E : (Fin n → ℕ) → Prop) {_ : DecidablePred E}
    (hE : ∀ v, E v → 10 * absv v < 19 * n)
    (hbox : ∑ w ∈ (Box n (3 * n)).filter (fun w => 10 * (∑ i, w i) < 19 * n),
      ((1 : ℝ) / 2) ^ (∑ i, w i) ≤ Real.exp (-(n : ℝ) / 2400)) :
    ∑ v ∈ (Tset n).filter E, ((1 : ℝ) / 2) ^ absv v ≤ Real.exp (-(n : ℝ) / 2400) := by
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity)) hbox
  intro w hw
  rw [Finset.mem_filter] at hw ⊢
  exact ⟨(Finset.mem_filter.1 hw.1).1, hE w hw.2⟩

lemma p119_n {x y : ℝ} {n : ℕ} (hn : 5 ≤ n) (hx : (2 : ℝ) ^ (10 * n) ≤ x) (hy0 : 0 ≤ y)
    (hy : (y ^ alph) ^ 10 ≤ x ^ 10 * 2 ^ n) (hK : (2 : ℝ) ^ (6 * n + 1) ≤ ⌈y⌉₊ * Z y)
    (E : (Fin n → ℕ) → Prop) {_ : DecidablePred E} (hE : ∀ v, E v ↔ 10 * absv v < 19 * n)
    (h19 : |prob y (fun N => E (vecn n N)) - ∑ v ∈ (Tset n).filter E, ((1 : ℝ) / 2) ^ absv v| ≤
      (2 * (2 ^ (6 * n + 1) / ((⌈y⌉₊ : ℝ) * Z y)) + 2) * (8 / 9) ^ n)
    (htail : ∑ v ∈ (Tset n).filter E, ((1 : ℝ) / 2) ^ absv v ≤ Real.exp (-(n : ℝ) / 2400)) :
    prob y (fun N => ¬ Reaches x N) ≤ 4 * (8 / 9) ^ n + Real.exp (-(n : ℝ) / 2400) := by
  have hmono : prob y (fun N => ¬ Reaches x N) ≤ prob y (fun N => E (vecn n N)) := by
    unfold prob
    apply div_le_div_of_nonneg_right _ (Z_nonneg y)
    apply Finset.sum_le_sum; intro N hN
    by_cases h1 : ¬ Reaches x N
    · rw [if_pos h1, if_pos ((hE _).2 (small_of_notReach hn hx hy0 hy hN h1))]
    · rw [if_neg h1]; split_ifs <;> positivity
  have hq : (2 : ℝ) ^ (6 * n + 1) / ((⌈y⌉₊ : ℝ) * Z y) ≤ 1 :=
    div_le_one_of_le₀ hK (mul_nonneg (Nat.cast_nonneg _) (Z_nonneg y))
  have h89 : (0 : ℝ) ≤ (8 / 9) ^ n := by positivity
  have hab := (abs_le.1 h19).2
  have herr : (2 * (2 ^ (6 * n + 1) / ((⌈y⌉₊ : ℝ) * Z y)) + 2) * (8 / 9) ^ n ≤ 4 * (8 / 9) ^ n :=
    mul_le_mul_of_nonneg_right (by linarith) h89
  linarith

set_option maxHeartbeats 1000000 in
/-- Parameter sizes for `n = ⌊log x / (10 log 2)⌋` (Tao (5.1)) and `y ∈ [x, x^{α²}]`, `x ≥ e^6000`. -/
lemma sizes_of_x (x y : ℝ) (n : ℕ) (hx : Real.exp 6000 ≤ x) (hxy : x ≤ y) (hyx : y ≤ x ^ (alph ^ 2))
    (hn : n = ⌊Real.log x / (10 * Real.log 2)⌋₊) :
    5 ≤ n ∧ (n : ℝ) ≤ Real.log x ∧ (2 : ℝ) ^ (10 * n) ≤ x ∧ (y ^ alph) ^ 10 ≤ x ^ 10 * 2 ^ n ∧
    (2 : ℝ) ^ (6 * n + 1) ≤ ⌈y⌉₊ * Z y ∧ 2 * 2 ^ (3 * n) ≤ ⌈y⌉₊ ∧ 0 < Z y ∧
    ((8 : ℝ) / 9) ^ n ≤ Real.exp (-(n : ℝ) / 2400) ∧
    Real.exp (-(n : ℝ) / 2400) ≤ 2 * x ^ (-(1 / 20000 : ℝ)) := by
  have l2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have l2u := Real.log_two_lt_d9
  have hx1 : (1 : ℝ) ≤ x := le_trans (Real.one_le_exp (by norm_num)) hx
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := by linarith
  have hpow : ∀ k : ℕ, (2 : ℝ) ^ k = Real.exp (k * Real.log 2) := by
    intro k; rw [← Real.log_pow, Real.exp_log (by positivity)]
  have hLx : (6000 : ℝ) ≤ Real.log x := by
    have := Real.log_le_log (Real.exp_pos _) hx
    rwa [Real.log_exp] at this
  have hLy : Real.log x ≤ Real.log y := Real.log_le_log hx0 hxy
  have hq0 : 0 ≤ Real.log x / (10 * Real.log 2) := div_nonneg (by linarith) (by positivity)
  have hn1 : (n : ℝ) ≤ Real.log x / (10 * Real.log 2) := hn ▸ Nat.floor_le hq0
  have hn2 : Real.log x / (10 * Real.log 2) < n + 1 := hn ▸ Nat.lt_floor_add_one _
  have hlo : 10 * n * Real.log 2 ≤ Real.log x := by
    rw [le_div_iff₀ (by positivity)] at hn1; linarith
  have hhi : Real.log x < 10 * (n + 1) * Real.log 2 := by
    rw [div_lt_iff₀ (by positivity)] at hn2; linarith
  have hn5 : 5 ≤ n := by
    have h300 : (857 : ℝ) < n + 1 := by
      by_contra h; push_neg at h
      have := mul_le_mul_of_nonneg_right h l2.le
      linarith
    have : (5 : ℝ) ≤ n := by linarith
    exact_mod_cast this
  have hnR : (5 : ℝ) ≤ n := by exact_mod_cast hn5
  have hnl : Real.log 2 ≤ n * Real.log 2 := by (first | linarith | nlinarith)
  -- (a) 2^{10n} ≤ x ≤ y
  have h2x : (2 : ℝ) ^ (10 * n) ≤ x := by
    rw [hpow]
    calc Real.exp (((10 * n : ℕ) : ℝ) * Real.log 2) ≤ Real.exp (Real.log x) :=
          Real.exp_le_exp.2 (by push_cast; linarith)
      _ = x := Real.exp_log hx0
  -- (b) (y^α)^10 ≤ x^10 2^n
  have hyb : (y ^ alph) ^ 10 ≤ x ^ 10 * 2 ^ n := by
    have hly : Real.log y ≤ alph ^ 2 * Real.log x := by
      have := Real.log_le_log hy0 hyx
      rwa [Real.log_rpow hx0] at this
    rw [← Real.log_le_log_iff (by positivity) (by positivity), Real.log_pow, Real.log_rpow hy0,
      Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
    unfold alph at hly ⊢
    push_cast
    (first | linarith | nlinarith)
  -- (c) Z y ≥ 1/3 and hK
  have hZ3 : 1 / 3 ≤ Z y := by
    apply Z_ge (by linarith)
    have hsplit : y ^ alph = y * Real.exp (Real.log y / 1000) := by
      rw [Real.rpow_def_of_pos hy0, show Real.log y * alph = Real.log y + Real.log y / 1000 by
        unfold alph; ring, Real.exp_add, Real.exp_log hy0]
    have h8 : (7 : ℝ) ≤ Real.exp (Real.log y / 1000) := by
      have := Real.add_one_le_exp (Real.log y / 1000)
      linarith
    rw [hsplit]; (first | linarith [mul_le_mul_of_nonneg_left h8 hy0.le] | nlinarith [mul_le_mul_of_nonneg_left h8 hy0.le])
  have hZ : 0 < Z y := by linarith
  have hcy : y ≤ (⌈y⌉₊ : ℝ) := Nat.le_ceil y
  have h6 : (2 : ℝ) ^ (6 * n + 1) * 3 ≤ 2 ^ (10 * n) := by
    have : (2 : ℝ) ^ (10 * n) = 2 ^ (6 * n + 1) * 2 ^ (4 * n - 1) := by
      rw [← pow_add]; congr 1; omega
    rw [this]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    calc (3 : ℝ) ≤ 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (4 * n - 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hK : (2 : ℝ) ^ (6 * n + 1) ≤ ⌈y⌉₊ * Z y := by
    have := mul_le_mul_of_nonneg_left hZ3 (show (0 : ℝ) ≤ ⌈y⌉₊ by positivity)
    linarith
  have hM : 2 * 2 ^ (3 * n) ≤ ⌈y⌉₊ := by
    have h1 : (2 : ℝ) * 2 ^ (3 * n) ≤ 2 ^ (10 * n) := by
      rw [← pow_succ']; exact pow_le_pow_right₀ (by norm_num) (by omega)
    have : ((2 * 2 ^ (3 * n) : ℕ) : ℝ) ≤ ⌈y⌉₊ := by push_cast; linarith
    exact_mod_cast this
  have hnlog : (n : ℝ) ≤ Real.log x :=
    le_trans hn1 (div_le_self (by linarith) (by linarith [Real.log_two_gt_d9]))
  -- (d) 4 (8/9)^n + e^{-n/2400} ≤ 10 x^{-1/20000}
  have h89 : ((8 : ℝ) / 9) ^ n ≤ Real.exp (-(n : ℝ) / 2400) := by
    have h1 : (8 : ℝ) / 9 ≤ Real.exp (-1 / 2400) := by
      have := Real.add_one_le_exp (-1 / 2400 : ℝ); linarith
    calc ((8 : ℝ) / 9) ^ n ≤ Real.exp (-1 / 2400) ^ n := pow_le_pow_left₀ (by norm_num) h1 n
      _ = Real.exp (-(n : ℝ) / 2400) := by rw [← Real.exp_nat_mul]; congr 1; ring
  have hfin : Real.exp (-(n : ℝ) / 2400) ≤ 2 * x ^ (-(1 / 20000 : ℝ)) := by
    rw [Real.rpow_def_of_pos hx0]
    calc Real.exp (-(n : ℝ) / 2400) ≤ Real.exp (Real.log 2 + Real.log x * -(1 / 20000)) := by
          apply Real.exp_le_exp.2
          have := mul_le_mul_of_nonneg_left l2u.le (show (0 : ℝ) ≤ n by positivity)
          (first | linarith | nlinarith)
      _ = 2 * Real.exp (Real.log x * -(1 / 20000)) := by
          rw [Real.exp_add, Real.exp_log (by norm_num)]
  exact ⟨hn5, hnlog, h2x, hyb, hK, hM, hZ, h89, hfin⟩

set_option maxHeartbeats 1000000 in
open Classical in
/-- Tao (1.19) for every `y ∈ [x, x^{α²}]` (so for `y = x^α` and `y = x^{α²}`), from Prop 1.9 for `N_y`
(`prop19_Ny`) and the lower tail `box_tail19`, both passed as hypotheses (discharged in the merged file). -/
theorem p119
    (h19 : ∀ (y : ℝ) (n : ℕ), 1 ≤ n → 2 * 2 ^ (3 * n) ≤ ⌈y⌉₊ → 0 < Z y →
      ∀ E : (Fin n → ℕ) → Prop,
      |prob y (fun N => E (vecn n N)) - ∑ v ∈ (Tset n).filter E, ((1 : ℝ) / 2) ^ absv v| ≤
        (2 * (2 ^ (6 * n + 1) / ((⌈y⌉₊ : ℝ) * Z y)) + 2) * (8 / 9) ^ n)
    (hbox : ∀ n : ℕ, 1 ≤ n →
      ∑ w ∈ (Box n (3 * n)).filter (fun w => 10 * (∑ i, w i) < 19 * n),
        ((1 : ℝ) / 2) ^ (∑ i, w i) ≤ Real.exp (-(n : ℝ) / 2400)) :
    ∃ C c x0 : ℝ, 0 < C ∧ 0 < c ∧ ∀ x : ℝ, x0 ≤ x → ∀ y : ℝ, x ≤ y → y ≤ x ^ (alph ^ 2) →
      prob y (fun N => ¬ Reaches x N) ≤ C * x ^ (-c) := by
  refine ⟨10, 1 / 20000, Real.exp 6000, by norm_num, by norm_num, ?_⟩
  intro x hx y hxy hyx
  obtain ⟨n, hn⟩ : ∃ n : ℕ, n = ⌊Real.log x / (10 * Real.log 2)⌋₊ := ⟨_, rfl⟩
  obtain ⟨hn5, -, h2x, hyb, hK, hM, hZ, h89, hfin⟩ := sizes_of_x x y n hx hxy hyx hn
  have hy0 : (0 : ℝ) ≤ y := le_trans (le_trans (Real.exp_pos 6000).le hx) hxy
  have hbase := p119_n hn5 h2x hy0 hyb hK (fun v => 10 * absv v < 19 * n) (fun v => Iff.rfl)
    (h19 y n (by omega) hM hZ (fun v => 10 * absv v < 19 * n))
    (tset_tail n (fun v => 10 * absv v < 19 * n) (fun v h => h) (hbox n (by omega)))
  linarith

end Item6a3

/-! ## S14: DECOMPOSE item 6b (Tao (5.12)): the deviation event for `N_y`.
Copies of `ps`, `padv`, `DevOK` from `_syr.lean` (identical definitions; drop these copies when merging). -/

def ps (a : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | j + 1 => ps a j + a j

def padv {n : ℕ} (w : Fin n → ℕ) : ℕ → ℕ := fun i => if h : i < n then w ⟨i, h⟩ else 1

def DevOK (C L : ℝ) (a : ℕ → ℕ) (k : ℕ) : Prop :=
  ∀ j ∈ Finset.Icc 1 k, |(ps a j : ℝ) - 2 * j| ≤ C * (Real.sqrt (j * L) + L)

section Item6b
open Classical

/-- Prefix sums of the padded valuation vector are the `A`-statistics of the orbit. -/
lemma ps_padv_vecn (n N : ℕ) : ∀ j, j ≤ n → ps (padv (vecn n N)) j = A N j := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
    intro hj
    show ps (padv (vecn n N)) j + padv (vecn n N) j = A N j + a (syracuseStep^[j] N)
    rw [ih (by omega)]
    simp [padv, show j < n by omega, vecn]

/-- `DevOK` for the valuation vector of `N` is the deviation bound for `A N j`. -/
lemma devOK_vecn_iff (C L : ℝ) (n N : ℕ) :
    DevOK C L (padv (vecn n N)) n ↔
      ∀ j ∈ Finset.Icc 1 n, |(A N j : ℝ) - 2 * j| ≤ C * (Real.sqrt (j * L) + L) := by
  unfold DevOK
  constructor
  · intro h j hj
    rw [← ps_padv_vecn n N j (Finset.mem_Icc.1 hj).2]; exact h j hj
  · intro h j hj
    rw [ps_padv_vecn n N j (Finset.mem_Icc.1 hj).2]; exact h j hj

/-- Tao (5.12) core: `P(N_y has a prefix deviation) ≤ 4 (8/9)^n + 2n e^{-CL/24}`, from Prop 1.9 for `N_y`
(hypothesis `h19`, the `prop19_Ny` instance) and the box bound `dev_bad_mass` (hypothesis `hdev`). -/
lemma p512_n {y : ℝ} {n : ℕ} (C L : ℝ) (hK : (2 : ℝ) ^ (6 * n + 1) ≤ ⌈y⌉₊ * Z y)
    (h19 : |prob y (fun N => ¬ DevOK C L (padv (vecn n N)) n) -
        ∑ v ∈ (Tset n).filter (fun v => ¬ DevOK C L (padv v) n), ((1 : ℝ) / 2) ^ absv v| ≤
      (2 * (2 ^ (6 * n + 1) / ((⌈y⌉₊ : ℝ) * Z y)) + 2) * (8 / 9) ^ n)
    (hdev : ∑ w ∈ (Box n (3 * n)).filter (fun w => ¬ DevOK C L (padv w) n),
      ((1 : ℝ) / 2) ^ (∑ i, w i) ≤ 2 * n * Real.exp (-(C * L) / 24)) :
    prob y (fun N => ¬ ∀ j ∈ Finset.Icc 1 n, |(A N j : ℝ) - 2 * j| ≤ C * (Real.sqrt (j * L) + L)) ≤
      4 * (8 / 9) ^ n + 2 * n * Real.exp (-(C * L) / 24) := by
  have heq : prob y (fun N => ¬ ∀ j ∈ Finset.Icc 1 n, |(A N j : ℝ) - 2 * j| ≤ C * (Real.sqrt (j * L) + L)) =
      prob y (fun N => ¬ DevOK C L (padv (vecn n N)) n) := by
    unfold prob; congr 1; apply Finset.sum_congr rfl; intro N _
    beta_reduce
    by_cases h : DevOK C L (padv (vecn n N)) n
    · rw [if_neg (not_not.2 ((devOK_vecn_iff C L n N).1 h)), if_neg (not_not.2 h)]
    · rw [if_pos (fun h2 => h ((devOK_vecn_iff C L n N).2 h2)), if_pos h]
  rw [heq]
  have htail : ∑ v ∈ (Tset n).filter (fun v => ¬ DevOK C L (padv v) n), ((1 : ℝ) / 2) ^ absv v ≤
      2 * n * Real.exp (-(C * L) / 24) := by
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity)) hdev
    intro w hw
    rw [Finset.mem_filter] at hw ⊢
    exact ⟨(Finset.mem_filter.1 hw.1).1, hw.2⟩
  have hq : (2 : ℝ) ^ (6 * n + 1) / ((⌈y⌉₊ : ℝ) * Z y) ≤ 1 :=
    div_le_one_of_le₀ hK (mul_nonneg (Nat.cast_nonneg _) (Z_nonneg y))
  have h89 : (0 : ℝ) ≤ (8 / 9) ^ n := by positivity
  have hab := (abs_le.1 h19).2
  have herr : (2 * (2 ^ (6 * n + 1) / ((⌈y⌉₊ : ℝ) * Z y)) + 2) * (8 / 9) ^ n ≤ 4 * (8 / 9) ^ n :=
    mul_le_mul_of_nonneg_right (by linarith) h89
  linarith


set_option maxHeartbeats 1000000 in
/-- Tao (5.12) with explicit error: for `x ≥ e^6000`, `y ∈ [x, x^{α²}]`, `n0 = ⌊log x/(10 log 2)⌋`,
`P(∃ j ≤ n0, |A N_y j - 2j| > 2 log^{3/5} x) ≤ 8 x^{-1/20000} + 2 log x · exp(-log^{1/5} x / 24)`
(the right side is `≪ log^{-10} x`). Hypotheses `h19` (= `prop19_Ny`) and `hdev` (= `dev_bad_mass` at `K = 3n`). -/
theorem p512
    (h19 : ∀ (y : ℝ) (n : ℕ), 1 ≤ n → 2 * 2 ^ (3 * n) ≤ ⌈y⌉₊ → 0 < Z y →
      ∀ E : (Fin n → ℕ) → Prop,
      |prob y (fun N => E (vecn n N)) - ∑ v ∈ (Tset n).filter E, ((1 : ℝ) / 2) ^ absv v| ≤
        (2 * (2 ^ (6 * n + 1) / ((⌈y⌉₊ : ℝ) * Z y)) + 2) * (8 / 9) ^ n)
    (hdev : ∀ (n : ℕ) (C L : ℝ), 1 ≤ C → 0 ≤ L →
      ∑ w ∈ (Box n (3 * n)).filter (fun w => ¬ DevOK C L (padv w) n),
        ((1 : ℝ) / 2) ^ (∑ i, w i) ≤ 2 * n * Real.exp (-(C * L) / 24))
    (x : ℝ) (hx : Real.exp 6000 ≤ x) (y : ℝ) (hxy : x ≤ y) (hyx : y ≤ x ^ (alph ^ 2)) :
    prob y (fun N => ¬ ∀ j ∈ Finset.Icc 1 ⌊Real.log x / (10 * Real.log 2)⌋₊,
        |(A N j : ℝ) - 2 * j| ≤ 2 * Real.log x ^ ((3 : ℝ) / 5)) ≤
      8 * x ^ (-(1 / 20000 : ℝ)) + 2 * Real.log x * Real.exp (-(Real.log x ^ ((1 : ℝ) / 5)) / 24) := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, n = ⌊Real.log x / (10 * Real.log 2)⌋₊ := ⟨_, rfl⟩
  rw [← hn]
  obtain ⟨hn5, hnlog, -, -, hK, hM, hZ, h89, hfin⟩ := sizes_of_x x y n hx hxy hyx hn
  have hu1 : 1 ≤ Real.log x := by
    have := Real.log_le_log (Real.exp_pos _) hx
    rw [Real.log_exp] at this; linarith
  set u := Real.log x with hu_def
  have hu0 : 0 < u := by linarith
  set L := u ^ ((1 : ℝ) / 5) with hL_def
  have hL0 : 0 ≤ L := by positivity
  have hLu : L ≤ u ^ ((3 : ℝ) / 5) := Real.rpow_le_rpow_of_exponent_le hu1 (by norm_num)
  have hsq : (u ^ ((3 : ℝ) / 5)) ^ 2 = u * L := by
    rw [sq, ← Real.rpow_add hu0, hL_def,
      show (3 : ℝ) / 5 + 3 / 5 = 1 + 1 / 5 by norm_num, Real.rpow_add hu0, Real.rpow_one]
  have hthr : ∀ j ∈ Finset.Icc 1 n, (1 : ℝ) * (Real.sqrt (j * L) + L) ≤ 2 * u ^ ((3 : ℝ) / 5) := by
    intro j hj
    have hjn : (j : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.1 hj).2
    have hjL : (j : ℝ) * L ≤ (u ^ ((3 : ℝ) / 5)) ^ 2 := by
      rw [hsq]; exact mul_le_mul_of_nonneg_right (hjn.trans hnlog) hL0
    have hs : Real.sqrt (j * L) ≤ u ^ ((3 : ℝ) / 5) :=
      (Real.sqrt_le_sqrt hjL).trans_eq (Real.sqrt_sq (by positivity))
    linarith
  have hmono : prob y (fun N => ¬ ∀ j ∈ Finset.Icc 1 n, |(A N j : ℝ) - 2 * j| ≤ 2 * u ^ ((3 : ℝ) / 5)) ≤
      prob y (fun N => ¬ ∀ j ∈ Finset.Icc 1 n, |(A N j : ℝ) - 2 * j| ≤ 1 * (Real.sqrt (j * L) + L)) :=
    prob_mono y (fun N hN h => hN (fun j hj => (h j hj).trans (hthr j hj)))
  have h19' := h19 y n (by omega) hM hZ (fun v => ¬ DevOK 1 L (padv v) n)
  have hbase := p512_n 1 L hK (by convert h19') (hdev n 1 L le_rfl hL0)
  have hlast : 2 * (n : ℝ) * Real.exp (-(1 * L) / 24) ≤ 2 * u * Real.exp (-L / 24) := by
    rw [one_mul]; exact mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
  linarith

end Item6b

/-! ## S15: DECOMPOSE item 6c1 (Tao (5.13)/(5.14)): deterministic orbit approximation on the deviation-good event. -/
section Item6c

/-- Tao (5.14), deterministic: if `|A_k(N) - 2k| ≤ D` and `4^k ≤ N`, then
`log Syr^k(N) = log N + k log(3/4) + O((2D+1) log 2)`. -/
lemma log_syr_approx (N k : ℕ) (D : ℝ) (hD : 0 ≤ D) (hN : (4 : ℝ) ^ k ≤ N)
    (hdev : |(A N k : ℝ) - 2 * k| ≤ D) :
    |Real.log (syracuseStep^[k] N : ℝ) - (Real.log N + k * Real.log (3 / 4))| ≤
      (2 * D + 1) * Real.log 2 := by
  have l2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hN1 : (1 : ℝ) ≤ N := le_trans (one_le_pow₀ (by norm_num)) hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hf : (2 : ℝ) ^ (A N k) * (syracuseStep^[k] N : ℝ) = 3 ^ k * N + S N k := by
    exact_mod_cast iterate_formula N k
  have h2 : 2 * (S N k : ℝ) + 2 ^ (A N k) ≤ 3 ^ k * 2 ^ (A N k) := by
    exact_mod_cast two_S_add_le N k
  set s : ℝ := (syracuseStep^[k] N : ℝ) with hs_def
  set P : ℝ := (2 : ℝ) ^ (A N k) with hP_def
  have hP : 0 < P := by positivity
  have hS0 : (0 : ℝ) ≤ S N k := Nat.cast_nonneg _
  have h3 : (0 : ℝ) < 3 ^ k := by positivity
  have hsP_lo : 3 ^ k * (N : ℝ) ≤ P * s := by rw [hf]; linarith
  have hs0 : 0 < s := by
    have h0 : 0 < P * s := lt_of_lt_of_le (by positivity) hsP_lo
    by_contra hc; push_neg at hc
    have := mul_nonpos_of_nonneg_of_nonpos hP.le hc
    linarith
  have hsP_hi : P * s ≤ 3 ^ k * N + 3 ^ k * P / 2 := by rw [hf]; linarith
  have hlogPs : Real.log (P * s) = A N k * Real.log 2 + Real.log s := by
    rw [Real.log_mul hP.ne' hs0.ne', hP_def, Real.log_pow]
  have hlog3N : Real.log (3 ^ k * N) = k * Real.log 3 + Real.log N := by
    rw [Real.log_mul (by positivity) hN0.ne', Real.log_pow]
  have h34 : Real.log (3 / 4 : ℝ) = Real.log 3 - 2 * Real.log 2 := by
    rw [Real.log_div (by norm_num) (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast; ring
  have hdl := abs_le.1 hdev
  have m1 : ((A N k : ℝ) - 2 * k) * Real.log 2 ≤ D * Real.log 2 :=
    mul_le_mul_of_nonneg_right hdl.2 l2.le
  have m2 : -D * Real.log 2 ≤ ((A N k : ℝ) - 2 * k) * Real.log 2 :=
    mul_le_mul_of_nonneg_right hdl.1 l2.le
  have hlo : k * Real.log 3 + Real.log N ≤ A N k * Real.log 2 + Real.log s := by
    rw [← hlogPs, ← hlog3N]; exact Real.log_le_log (by positivity) hsP_lo
  set E : ℝ := Real.exp (D * Real.log 2) with hE_def
  have hE1 : 1 ≤ E := Real.one_le_exp (by positivity)
  have hPN : P ≤ E * N := by
    have e1 : P = Real.exp (A N k * Real.log 2) := by
      rw [show (A N k : ℝ) * Real.log 2 = Real.log P by rw [hP_def, Real.log_pow]]
      exact (Real.exp_log hP).symm
    have e2 : (4 : ℝ) ^ k = Real.exp (2 * k * Real.log 2) := by
      rw [show (2 * k * Real.log 2 : ℝ) = Real.log ((4 : ℝ) ^ k) by
        rw [Real.log_pow, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring]
      exact (Real.exp_log (by positivity)).symm
    calc P = Real.exp (A N k * Real.log 2) := e1
      _ ≤ Real.exp (D * Real.log 2 + 2 * k * Real.log 2) := Real.exp_le_exp.2 (by linarith)
      _ = E * 4 ^ k := by rw [Real.exp_add, e2]
      _ ≤ E * N := mul_le_mul_of_nonneg_left hN (by positivity)
  have i1 : 3 ^ k * P ≤ 3 ^ k * N * E := by
    have := mul_le_mul_of_nonneg_left hPN h3.le
    linarith [show (3 : ℝ) ^ k * (E * N) = 3 ^ k * N * E by ring]
  have i2 : 3 ^ k * (N : ℝ) ≤ 3 ^ k * N * E := by
    simpa using mul_le_mul_of_nonneg_left hE1 (by positivity : (0 : ℝ) ≤ 3 ^ k * N)
  have hhi' : P * s ≤ 3 ^ k * N * (2 * E) := by
    have : (3 : ℝ) ^ k * N * (2 * E) = 2 * (3 ^ k * N * E) := by ring
    linarith
  have hup : A N k * Real.log 2 + Real.log s ≤ k * Real.log 3 + Real.log N + (Real.log 2 + D * Real.log 2) := by
    rw [← hlogPs]
    calc Real.log (P * s) ≤ Real.log (3 ^ k * N * (2 * E)) := Real.log_le_log (by positivity) hhi'
      _ = k * Real.log 3 + Real.log N + (Real.log 2 + D * Real.log 2) := by
        rw [Real.log_mul (by positivity) (by positivity), hlog3N,
          Real.log_mul (by norm_num) (by positivity), hE_def, Real.log_exp]
  rw [h34, abs_le]
  constructor <;> (first | linarith [m1, m2, hlo, hup, l2] | nlinarith [m1, m2, hlo, hup, l2])


-- Copies of the main draft's `T` and `T_le` (drop both when merging).
open Classical in
noncomputable def T (x : ℝ) (N : ℕ) : ℕ := if h : Reaches x N then Nat.find h else 0

lemma T_le (x : ℝ) (N n : ℕ) (h : (syracuseStep^[n] N : ℝ) ≤ x) : T x N ≤ n := by
  have hr : Reaches x N := ⟨n, h⟩
  unfold T; rw [dif_pos hr]; exact Nat.find_min' hr h

lemma T_spec (x : ℝ) (N : ℕ) (h : Reaches x N) : (syracuseStep^[T x N] N : ℝ) ≤ x := by
  unfold T; rw [dif_pos h]; exact Nat.find_spec h

lemma T_min (x : ℝ) (N : ℕ) (h : Reaches x N) (j : ℕ) (hj : j < T x N) :
    x < (syracuseStep^[j] N : ℝ) := by
  unfold T at hj; rw [dif_pos h] at hj
  exact not_le.1 (Nat.find_min h hj)

/-- Tao (5.15), deterministic: if the orbit tracks `log N + j log(3/4)` within `B` up to time `n0` and the
line is below `log x - B` at `n0`, then `T_x(N) ≤ n0` and `T_x(N) log(4/3) = log(N/x) + O(B + log(4/3))`. -/
lemma T_approx {x B : ℝ} {N n0 : ℕ} (hx1 : 1 ≤ x) (hxN : x ≤ N)
    (happ : ∀ j ≤ n0, |Real.log (syracuseStep^[j] N : ℝ) - (Real.log N + j * Real.log (3 / 4))| ≤ B)
    (hreach : Real.log N + n0 * Real.log (3 / 4) + B ≤ Real.log x) :
    Reaches x N ∧ T x N ≤ n0 ∧
      |(T x N : ℝ) * Real.log (4 / 3) - Real.log (N / x)| ≤ B + Real.log (4 / 3) := by
  have hx0 : 0 < x := by linarith
  have hN0 : (0 : ℝ) < N := by linarith
  have h43 : Real.log (3 / 4 : ℝ) = - Real.log (4 / 3) := by
    rw [show (3 / 4 : ℝ) = (4 / 3)⁻¹ by norm_num, Real.log_inv]
  have hl43 : 0 < Real.log (4 / 3 : ℝ) := Real.log_pos (by norm_num)
  have hNx : Real.log (N / x) = Real.log N - Real.log x := Real.log_div hN0.ne' hx0.ne'
  have hlx : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hle : ∀ s : ℝ, 0 ≤ s → s ≤ x → Real.log s ≤ Real.log x := by
    intro s hs0 hsx
    rcases hs0.lt_or_eq with h | h
    · exact Real.log_le_log h hsx
    · rw [← h, Real.log_zero]; exact hlx
  have hsn0 : (syracuseStep^[n0] N : ℝ) ≤ x := by
    have h := (abs_le.1 (happ n0 le_rfl)).2
    have hs0 : (0 : ℝ) ≤ (syracuseStep^[n0] N : ℝ) := Nat.cast_nonneg _
    rcases hs0.lt_or_eq with hpos | hz
    · have : Real.log (syracuseStep^[n0] N : ℝ) ≤ Real.log x := by linarith
      exact (Real.log_le_log_iff hpos hx0).1 this
    · rw [← hz]; exact hx0.le
  have hreachN : Reaches x N := ⟨n0, hsn0⟩
  have hTle : T x N ≤ n0 := T_le x N n0 hsn0
  have hspec := T_spec x N hreachN
  have hlo : Real.log N - (T x N : ℝ) * Real.log (4 / 3) - B ≤ Real.log x := by
    have h := (abs_le.1 (happ (T x N) hTle)).1
    have := hle _ (Nat.cast_nonneg _) hspec
    rw [h43] at h; linarith
  have hhi : (T x N : ℝ) * Real.log (4 / 3) ≤ Real.log N - Real.log x + B + Real.log (4 / 3) := by
    rcases Nat.eq_zero_or_pos (T x N) with h0 | hpos
    · rw [h0, Nat.cast_zero, zero_mul]
      have := Real.log_le_log hx0 hxN
      have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (happ 0 (Nat.zero_le _))
      linarith
    · have hgt := T_min x N hreachN (T x N - 1) (by omega)
      have hlog : Real.log x < Real.log (syracuseStep^[T x N - 1] N : ℝ) := Real.log_lt_log hx0 hgt
      have h := (abs_le.1 (happ (T x N - 1) (by omega))).2
      have hc : ((T x N - 1 : ℕ) : ℝ) = (T x N : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega), Nat.cast_one]
      rw [hc, h43] at h
      (first | linarith [hlog, h] | nlinarith [hlog, h])
  rw [hNx, abs_le]
  exact ⟨hreachN, hTle, by linarith, by linarith⟩


/-- (5.14) for all `j ≤ n0` on the deviation-good event of `p512` (prefix form `j ∈ [1, n0]`). -/
lemma approx_all (N n0 : ℕ) (D : ℝ) (hD : 0 ≤ D) (hN : (4 : ℝ) ^ n0 ≤ N)
    (hdev : ∀ j ∈ Finset.Icc 1 n0, |(A N j : ℝ) - 2 * j| ≤ D) :
    ∀ j ≤ n0, |Real.log (syracuseStep^[j] N : ℝ) - (Real.log N + j * Real.log (3 / 4))| ≤
      (2 * D + 1) * Real.log 2 := by
  intro j hj
  apply log_syr_approx N j D hD (le_trans (pow_le_pow_right₀ (by norm_num) hj) hN)
  rcases Nat.eq_zero_or_pos j with h0 | hpos
  · subst h0; simpa [A] using hD
  · exact hdev j (Finset.mem_Icc.2 ⟨hpos, hj⟩)

end Item6c

section Item6c3

/-- Copy of the main draft's `Pass` (drop when merging). -/
noncomputable def Pass (x : ℝ) (N : ℕ) : ℕ := syracuseStep^[T x N] N

lemma step_ne_zero (n : ℕ) : syracuseStep n ≠ 0 := by
  intro h
  have := two_pow_a_mul_step n
  rw [h, mul_zero] at this; omega

lemma iter_one_le {N : ℕ} (hN : 1 ≤ N) : ∀ j, 1 ≤ syracuseStep^[j] N := by
  intro j
  induction j with
  | zero => simpa using hN
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact Nat.one_le_iff_ne_zero.2 (step_ne_zero _)

/-- Tao's `E'` (5.10): first passage below `x` after exactly `m0` steps, landing in `E`,
starting within `exp(±W)` of `(4/3)^{m0} x`. -/
def Eprime (x : ℝ) (m0 : ℕ) (W : ℝ) (E : ℕ → Prop) (M : ℕ) : Prop :=
  Reaches x M ∧ T x M = m0 ∧ E (Pass x M) ∧
    |Real.log M - (Real.log x + m0 * Real.log (4 / 3))| ≤ W

lemma iter_comp (i k N : ℕ) : syracuseStep^[i] (syracuseStep^[k] N) = syracuseStep^[i + k] N :=
  (Function.iterate_add_apply _ _ _ _).symm

/-- Tao Sec 5 event identity (proof of Prop 5.2): on the (5.14)-good event, for `m0 ≤ n ≤ n0`,
`T_x(N) = n ∧ Pass_x(N) ∈ E` holds iff `Syr^{n-m0}(N) ∈ E'`. -/
lemma event_iff {x B W : ℝ} {N n0 m0 n : ℕ} (E : ℕ → Prop) (hx : 0 < x) (hN : 1 ≤ N)
    (happ : ∀ j ≤ n0, |Real.log (syracuseStep^[j] N : ℝ) - (Real.log N + j * Real.log (3 / 4))| ≤ B)
    (hm0 : 1 ≤ m0) (hmn : m0 ≤ n) (hn0 : n ≤ n0)
    (hW : 2 * B + Real.log (4 / 3) ≤ W) (hWm : W + 2 * B < m0 * Real.log (4 / 3)) :
    (Reaches x N ∧ T x N = n ∧ E (Pass x N)) ↔ Eprime x m0 W E (syracuseStep^[n - m0] N) := by
  have h43 : Real.log (3 / 4 : ℝ) = - Real.log (4 / 3) := by
    rw [show (3 / 4 : ℝ) = (4 / 3)⁻¹ by norm_num, Real.log_inv]
  have hl43 : 0 < Real.log (4 / 3 : ℝ) := Real.log_pos (by norm_num)
  have hpos : ∀ j, (0 : ℝ) < (syracuseStep^[j] N : ℝ) := fun j => by
    have := iter_one_le hN j; exact_mod_cast this
  have hlogle : ∀ j, (syracuseStep^[j] N : ℝ) ≤ x → Real.log (syracuseStep^[j] N : ℝ) ≤ Real.log x :=
    fun j h => Real.log_le_log (hpos j) h
  have hMn : syracuseStep^[m0] (syracuseStep^[n - m0] N) = syracuseStep^[n] N := by
    rw [iter_comp, Nat.add_sub_cancel' hmn]
  have hap : ∀ j ≤ n0, Real.log N - j * Real.log (4 / 3) - B ≤ Real.log (syracuseStep^[j] N : ℝ) ∧
      Real.log (syracuseStep^[j] N : ℝ) ≤ Real.log N - j * Real.log (4 / 3) + B := by
    intro j hj
    have h := abs_le.1 (happ j hj); rw [h43] at h
    constructor <;> linarith [h.1, h.2]
  have hc2 : ((n - m0 : ℕ) : ℝ) = (n : ℝ) - m0 := Nat.cast_sub hmn
  constructor
  · rintro ⟨hR, hT, hE⟩
    have hsn : (syracuseStep^[n] N : ℝ) ≤ x := by rw [← hT]; exact T_spec x N hR
    have hRM : Reaches x (syracuseStep^[n - m0] N) := ⟨m0, by rw [hMn]; exact hsn⟩
    have hTM : T x (syracuseStep^[n - m0] N) = m0 := by
      apply le_antisymm (T_le x _ m0 (by rw [hMn]; exact hsn))
      have h1 := T_spec x _ hRM
      rw [iter_comp] at h1
      have h2 := T_le x N _ h1
      omega
    have hPass : Pass x (syracuseStep^[n - m0] N) = Pass x N := by
      unfold Pass; rw [hTM, hMn, hT]
    refine ⟨hRM, hTM, hPass ▸ hE, ?_⟩
    have hgt := T_min x N hR (n - 1) (by omega)
    have hlog1 : Real.log x < Real.log (syracuseStep^[n - 1] N : ℝ) := Real.log_lt_log hx hgt
    have hlog2 := hlogle n hsn
    have hc1 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by rw [Nat.cast_sub (by omega), Nat.cast_one]
    have a1 := hap (n - 1) (by omega)
    have a2 := hap n hn0
    have a3 := hap (n - m0) (by omega)
    rw [hc1] at a1; rw [hc2] at a3
    rw [abs_le]; constructor <;> (first | linarith [a1.1, a1.2, a2.1, a2.2, a3.1, a3.2] | nlinarith [a1.1, a1.2, a2.1, a2.2, a3.1, a3.2])
  · rintro ⟨hRM, hTM, hE, hW'⟩
    have hsn : (syracuseStep^[n] N : ℝ) ≤ x := by
      rw [← hMn]; have := T_spec x _ hRM; rw [hTM] at this; exact this
    have hR : Reaches x N := ⟨n, hsn⟩
    have hT : T x N = n := by
      apply le_antisymm (T_le x N n hsn)
      by_contra hlt
      push_neg at hlt
      have hst := T_spec x N hR
      by_cases hcase : n - m0 ≤ T x N
      · have h1 : (syracuseStep^[T x N - (n - m0)] (syracuseStep^[n - m0] N) : ℝ) ≤ x := by
          rw [iter_comp, Nat.sub_add_cancel hcase]; exact hst
        have := T_le x _ _ h1
        omega
      · push_neg at hcase
        have a1 := hap (T x N) (by omega)
        have a3 := hap (n - m0) (by omega)
        rw [hc2] at a3
        have htle : ((T x N : ℕ) : ℝ) ≤ (n : ℝ) - m0 := by
          rw [← hc2]; exact_mod_cast hcase.le
        have hmul := mul_le_mul_of_nonneg_right htle hl43.le
        have hW2 := (abs_le.1 hW').1
        have := hlogle _ hst
        (first | linarith [a1.1, a3.2] | nlinarith [a1.1, a3.2])
    refine ⟨hR, hT, ?_⟩
    have hPass : Pass x N = Pass x (syracuseStep^[n - m0] N) := by
      unfold Pass; rw [hT, hTM, hMn]
    rw [hPass]; exact hE

end Item6c3

section Item6d

/-- Prefix sums shift along the orbit: `A_N(k + j) = A_N(k) + A_{Syr^k N}(j)`. -/
lemma A_shift (N k : ℕ) : ∀ j, A N (k + j) = A N k + A (syracuseStep^[k] N) j := by
  intro j
  induction j with
  | zero => rfl
  | succ j ih =>
    have h1 : A N (k + (j + 1)) = A N (k + j) + a (syracuseStep^[k + j] N) := rfl
    have h2 : A (syracuseStep^[k] N) (j + 1) =
        A (syracuseStep^[k] N) j + a (syracuseStep^[j] (syracuseStep^[k] N)) := rfl
    rw [h1, h2, ih, iter_comp, add_comm j k, add_assoc]

/-- Deviation transfer: a `D`-good prefix of `N` makes the shifted orbit `Syr^k N` `2D`-good. -/
lemma dev_shift (N k n0 : ℕ) (D : ℝ) (hD : 0 ≤ D)
    (hdev : ∀ j ∈ Finset.Icc 1 n0, |(A N j : ℝ) - 2 * j| ≤ D) :
    ∀ j, k + j ≤ n0 → |(A (syracuseStep^[k] N) j : ℝ) - 2 * j| ≤ 2 * D := by
  have h0 : ∀ i, i ≤ n0 → |(A N i : ℝ) - 2 * i| ≤ D := by
    intro i hi
    rcases Nat.eq_zero_or_pos i with h | h
    · subst h; simpa [A] using hD
    · exact hdev i (Finset.mem_Icc.2 ⟨h, hi⟩)
  intro j hj
  have e : (A (syracuseStep^[k] N) j : ℝ) = (A N (k + j) : ℝ) - A N k := by
    rw [A_shift N k j]; push_cast; ring
  have h1 := abs_le.1 (h0 (k + j) hj)
  have h2 := abs_le.1 (h0 k (by omega))
  rw [e, abs_le]; push_cast at h1 h2
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

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

lemma a_pos_of_odd {n : ℕ} (hn : Odd n) : 1 ≤ a n := by
  unfold a
  have h2 : 2 ∣ 3 * n + 1 := by
    obtain ⟨t, rfl⟩ := hn; exact ⟨3 * t + 2, by ring⟩
  exact Nat.Prime.factorization_pos_of_dvd Nat.prime_two (by omega) h2

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

lemma geo_one (K : ℕ) : ∑ j ∈ Finset.Icc 1 K, ((1 : ℝ) / 2) ^ j = 1 - (1 / 2) ^ K := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, pow_succ]; ring

lemma geo_two (K : ℕ) :
    ∑ j ∈ Finset.Icc 1 K, (j : ℝ) * ((1 : ℝ) / 2) ^ j = 2 - (K + 2) * (1 / 2) ^ K := by
  induction K with
  | zero => norm_num
  | succ K ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, pow_succ]; push_cast; ring

/-- `Σ_{b ∈ Box} 2^{-|b|} (2 + b_l) ≤ 4` (geometric weights, `E[Geom(2)] = 2`). -/
lemma sum_box_last (m K : ℕ) (l : Fin m) :
    ∑ b ∈ Box m K, ((1 : ℝ) / 2) ^ absv b * (2 + b l) ≤ 4 := by
  have key : ∀ b : Fin m → ℕ, ((1 : ℝ) / 2) ^ absv b * (2 + b l) =
      ∏ i, (((1 : ℝ) / 2) ^ b i * (if i = l then (2 + (b i : ℝ)) else 1)) := by
    intro b
    rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
    simp [absv]
  rw [Finset.sum_congr rfl (fun b _ => key b)]
  unfold Box
  rw [← Finset.prod_univ_sum (fun _ => Finset.Icc 1 K)
    (fun i j => ((1 : ℝ) / 2) ^ j * (if i = l then (2 + (j : ℝ)) else 1))]
  calc ∏ i, ∑ j ∈ Finset.Icc 1 K, ((1 : ℝ) / 2) ^ j * (if i = l then (2 + (j : ℝ)) else 1)
      ≤ ∏ i : Fin m, (if i = l then (4 : ℝ) else 1) := by
        apply Finset.prod_le_prod
        · intro i _; exact Finset.sum_nonneg (fun j _ => by split_ifs <;> positivity)
        · intro i _
          split_ifs with h
          · have e : ∑ j ∈ Finset.Icc 1 K, ((1 : ℝ) / 2) ^ j * (2 + (j : ℝ)) =
                2 * ∑ j ∈ Finset.Icc 1 K, ((1 : ℝ) / 2) ^ j +
                  ∑ j ∈ Finset.Icc 1 K, (j : ℝ) * ((1 : ℝ) / 2) ^ j := by
              rw [Finset.mul_sum, ← Finset.sum_add_distrib]
              exact Finset.sum_congr rfl (fun j _ => by ring)
            rw [e, geo_one, geo_two]
            have : (0 : ℝ) ≤ (1 / 2) ^ K := by positivity
            have : (0 : ℝ) ≤ (K + 2) * (1 / 2) ^ K := by positivity
            linarith
          · simp only [mul_one]; rw [geo_one]
            have : (0 : ℝ) ≤ (1 / 2) ^ K := by positivity
            linarith
    _ = 4 := by simp

/-- Tao Lemma 5.3 for one valuation block (proved in a separate child). -/
def CbS : Prop :=
  ∀ (x : ℝ) (hx : 0 < x) (m k : ℕ) (hm : 1 ≤ m) (b : Fin m → ℕ) (S : Finset ℕ) (hsize : 4 * (3 : ℝ) ^ (k + m) * 2 ^ (b ⟨m - 1, by omega⟩) ≤ x) (hS : ∀ M ∈ S, vecn m M = b ∧ (syracuseStep^[m] M : ℝ) ≤ x ∧ x < (syracuseStep^[m - 1] M : ℝ)) (hcong : ∀ M ∈ S, ∀ M' ∈ S, (3 : ℤ) ^ k ∣ (M' : ℤ) - M),
    (3 : ℝ) ^ k * ∑ M ∈ S, (1 : ℝ) / M ≤ ((1 : ℝ) / 2) ^ absv b * (2 + b ⟨m - 1, by omega⟩)

/-- Lemma 5.3, one valuation block `b = a⃗^{(m)}(M)`: the class sum is `≤ 2^{-|b|}(2 + b_m)`. -/
lemma cb_bound [hCb : Fact CbS] (x : ℝ) (hx : 0 < x) (m k : ℕ) (hm : 1 ≤ m) (b : Fin m → ℕ) (S : Finset ℕ) (hsize : 4 * (3 : ℝ) ^ (k + m) * 2 ^ (b ⟨m - 1, by omega⟩) ≤ x) (hS : ∀ M ∈ S, vecn m M = b ∧ (syracuseStep^[m] M : ℝ) ≤ x ∧ x < (syracuseStep^[m - 1] M : ℝ)) (hcong : ∀ M ∈ S, ∀ M' ∈ S, (3 : ℤ) ^ k ∣ (M' : ℤ) - M) :
    (3 : ℝ) ^ k * ∑ M ∈ S, (1 : ℝ) / M ≤ ((1 : ℝ) / 2) ^ absv b * (2 + b ⟨m - 1, by omega⟩) :=
  hCb.out x hx m k hm b S hsize hS hcong

/-- Tao Lemma 5.3 (on the deviation-restricted `E''`): `3^k Σ_{M ∈ S} 1/M ≤ 4` for a residue class
mod `3^k` of first-passage points with last valuation `a_{m} ≤ Dm`, when `4·3^{k+m}·2^{Dm} ≤ x`. -/
lemma c_bound [hCb : Fact CbS] (x : ℝ) (hx : 0 < x) (m k Dm : ℕ) (hm : 1 ≤ m)
    (hsize : 4 * (3 : ℝ) ^ (k + m) * 2 ^ Dm ≤ x) (S : Finset ℕ)
    (hS : ∀ M ∈ S, Odd M ∧ (syracuseStep^[m] M : ℝ) ≤ x ∧ x < (syracuseStep^[m - 1] M : ℝ) ∧
       a (syracuseStep^[m - 1] M) ≤ Dm)
    (hcong : ∀ M ∈ S, ∀ M' ∈ S, (3 : ℤ) ^ k ∣ (M' : ℤ) - M) :
    (3 : ℝ) ^ k * ∑ M ∈ S, (1 : ℝ) / M ≤ 4 := by
  rw [← Finset.sum_fiberwise_of_maps_to (fun M hM => Finset.mem_image_of_mem (vecn m) hM),
    Finset.mul_sum]
  obtain ⟨K, hK⟩ : ∃ K, ∀ b ∈ S.image (vecn m), ∀ i, b i ≤ K :=
    ⟨(S.image (vecn m)).sup (fun b => Finset.univ.sup b), fun b hb i =>
      le_trans (Finset.le_sup (f := b) (Finset.mem_univ i))
        (Finset.le_sup (f := fun b => Finset.univ.sup b) hb)⟩
  have hsub : S.image (vecn m) ⊆ Box m K := by
    intro b hb
    have hbK := hK b hb
    obtain ⟨M, hM, rfl⟩ := Finset.mem_image.1 hb
    unfold Box
    refine Fintype.mem_piFinset.2 (fun i => Finset.mem_Icc.2 ⟨?_, hbK i⟩)
    show 1 ≤ a (syracuseStep^[(i : ℕ)] M)
    apply a_pos_of_odd
    rcases Nat.eq_zero_or_pos (i : ℕ) with h0 | h0
    · rw [h0]; simpa using (hS M hM).1
    · exact iter_odd M i h0
  refine le_trans (Finset.sum_le_sum
    (g := fun b => ((1 : ℝ) / 2) ^ absv b * (2 + b ⟨m - 1, by omega⟩)) ?_) ?_
  · intro b hb
    obtain ⟨M₀, hM₀, rfl⟩ := Finset.mem_image.1 hb
    apply cb_bound x hx m k hm (vecn m M₀) _ ?_ ?_ ?_
    · calc 4 * (3 : ℝ) ^ (k + m) * 2 ^ (vecn m M₀ ⟨m - 1, by omega⟩)
          ≤ 4 * (3 : ℝ) ^ (k + m) * 2 ^ Dm :=
            mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) (hS M₀ hM₀).2.2.2)
              (by positivity)
        _ ≤ x := hsize
    · intro M hM
      obtain ⟨hMS, hMb⟩ := Finset.mem_filter.1 hM
      exact ⟨hMb, (hS M hMS).2.1, (hS M hMS).2.2.1⟩
    · intro M hM M' hM'
      exact hcong M (Finset.mem_filter.1 hM).1 M' (Finset.mem_filter.1 hM').1
  · exact le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity))
      (sum_box_last m K _)

end Item6d3

section ZAsymp

lemma tele (g : ℕ → ℝ) (J0 J1 : ℕ) (h : J0 ≤ J1) :
    ∑ j ∈ Finset.Ico J0 J1, (g (j + 1) - g j) = g J1 - g J0 := by
  obtain ⟨n, rfl⟩ : ∃ n, J1 = J0 + n := ⟨J1 - J0, by omega⟩
  clear h
  induction n with
  | zero => simp
  | succ n ih => rw [← add_assoc, Finset.sum_Ico_succ_top (by omega), ih]; ring

lemma oddIcc_eq (y : ℝ) : oddIcc y =
    (Finset.Ico (⌈y⌉₊ / 2) ((⌊y ^ alph⌋₊ + 1) / 2)).image (fun j => 2 * j + 1) := by
  ext N
  simp only [oddIcc, Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ico, Finset.mem_image,
    Nat.odd_iff]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨N / 2, ⟨by omega, by omega⟩, by omega⟩
  · rintro ⟨j, ⟨h1, h2⟩, rfl⟩
    omega

/-- Two-sided asymptotic for the normaliser: `Z y = (α-1)/2 · log y + O(1)`. -/
lemma Z_asymp {y : ℝ} (hy : 16 ≤ y) (hgap : y + 1 ≤ y ^ alph) :
    |Z y - (alph - 1) / 2 * Real.log y| ≤ 1 := by
  have hy0 : 0 < y := by linarith
  have hya : 0 < y ^ alph := Real.rpow_pos_of_pos hy0 _
  have hc1 : y ≤ (⌈y⌉₊ : ℝ) := Nat.le_ceil y
  have hc2 : (⌈y⌉₊ : ℝ) < y + 1 := Nat.ceil_lt_add_one hy0.le
  have hd1 : (⌊y ^ alph⌋₊ : ℝ) ≤ y ^ alph := Nat.floor_le hya.le
  have hd2 : y ^ alph < (⌊y ^ alph⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  have hcd : ⌈y⌉₊ ≤ ⌊y ^ alph⌋₊ + 1 := by
    have : (⌈y⌉₊ : ℝ) < ((⌊y ^ alph⌋₊ + 1 : ℕ) : ℝ) := by push_cast; linarith
    have := Nat.cast_lt.1 this
    omega
  have hc2' : 2 ≤ ⌈y⌉₊ := by
    have : (2 : ℝ) ≤ (⌈y⌉₊ : ℝ) := by linarith
    exact_mod_cast this
  obtain ⟨J0, hJ0⟩ : ∃ J0, J0 = ⌈y⌉₊ / 2 := ⟨_, rfl⟩
  obtain ⟨J1, hJ1⟩ : ∃ J1, J1 = (⌊y ^ alph⌋₊ + 1) / 2 := ⟨_, rfl⟩
  have hJ : J0 ≤ J1 := by omega
  have hJ0pos : 1 ≤ J0 := by omega
  have hZ : Z y = ∑ j ∈ Finset.Ico J0 J1, (1 : ℝ) / ((2 * j + 1 : ℕ) : ℝ) := by
    unfold Z; rw [oddIcc_eq, Finset.sum_image (fun a _ b _ h => by omega), hJ0, hJ1]
  have keyL : ∀ g : ℕ → ℝ, (∀ j, g (j + 1) - g j ≤ (1 : ℝ) / ((2 * j + 1 : ℕ) : ℝ)) →
      g J1 - g J0 ≤ Z y := fun g hg => by
    rw [hZ, ← tele g J0 J1 hJ]; exact Finset.sum_le_sum (fun j _ => hg j)
  have keyU : ∀ g : ℕ → ℝ, (∀ j, 1 ≤ j → (1 : ℝ) / ((2 * j + 1 : ℕ) : ℝ) ≤ g (j + 1) - g j) →
      Z y ≤ g J1 - g J0 := fun g hg => by
    rw [hZ, ← tele g J0 J1 hJ]
    exact Finset.sum_le_sum (fun j hj => hg j (le_trans hJ0pos (Finset.mem_Ico.1 hj).1))
  have hL := keyL (fun j => (1 / 2 : ℝ) * Real.log (2 * (j : ℝ) + 1)) (by
    intro j
    show (1 / 2 : ℝ) * Real.log (2 * ((j + 1 : ℕ) : ℝ) + 1) - 1 / 2 * Real.log (2 * (j : ℝ) + 1) ≤
      (1 : ℝ) / ((2 * j + 1 : ℕ) : ℝ)
    push_cast
    have hj : (0 : ℝ) < 2 * j + 1 := by positivity
    have h1 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (2 * j + 3) / (2 * j + 1) by positivity)
    rw [Real.log_div (by positivity) (by positivity)] at h1
    have e2 : (2 * (j : ℝ) + 3) / (2 * j + 1) - 1 = 2 * (1 / (2 * j + 1)) := by field_simp; ring
    rw [e2] at h1
    have e3 : (2 * ((j : ℝ) + 1) + 1) = 2 * j + 3 := by ring
    rw [e3]; linarith)
  have hU := keyU (fun j => (1 / 2 : ℝ) * Real.log (2 * (j : ℝ) - 1)) (by
    intro j hj1
    show (1 : ℝ) / ((2 * j + 1 : ℕ) : ℝ) ≤
      (1 / 2 : ℝ) * Real.log (2 * ((j + 1 : ℕ) : ℝ) - 1) - 1 / 2 * Real.log (2 * (j : ℝ) - 1)
    push_cast
    have hj1' : (1 : ℝ) ≤ j := by exact_mod_cast hj1
    have hjm : (0 : ℝ) < 2 * j - 1 := by linarith
    have hjp : (0 : ℝ) < 2 * j + 1 := by linarith
    have h1 := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < (2 * j + 1) / (2 * j - 1) by positivity)
    rw [Real.log_div hjp.ne' hjm.ne', inv_div] at h1
    have e2 : 1 - (2 * (j : ℝ) - 1) / (2 * j + 1) = 2 * (1 / (2 * j + 1)) := by field_simp; ring
    rw [e2] at h1
    have e3 : (2 * ((j : ℝ) + 1) - 1) = 2 * j + 1 := by ring
    rw [e3]; linarith)
  have hl2 := Real.log_two_lt_d9
  have hlogya : Real.log (y ^ alph) = alph * Real.log y := Real.log_rpow hy0 _
  -- lower: log(2 J1 + 1) ≥ alph log y, log(2 J0 + 1) ≤ log 2 + log y
  have a1 : y ^ alph ≤ 2 * (J1 : ℝ) + 1 := by
    have : ⌊y ^ alph⌋₊ + 1 ≤ 2 * J1 + 1 := by omega
    have : ((⌊y ^ alph⌋₊ + 1 : ℕ) : ℝ) ≤ ((2 * J1 + 1 : ℕ) : ℝ) := by exact_mod_cast this
    push_cast at this; linarith
  have a2 : 2 * (J0 : ℝ) + 1 ≤ 2 * y := by
    have : 2 * J0 ≤ ⌈y⌉₊ := by omega
    have : ((2 * J0 : ℕ) : ℝ) ≤ (⌈y⌉₊ : ℝ) := by exact_mod_cast this
    push_cast at this; linarith
  have a3 : 2 * (J1 : ℝ) - 1 ≤ y ^ alph := by
    have : 2 * J1 ≤ ⌊y ^ alph⌋₊ + 1 := by omega
    have : ((2 * J1 : ℕ) : ℝ) ≤ ((⌊y ^ alph⌋₊ + 1 : ℕ) : ℝ) := by exact_mod_cast this
    push_cast at this; linarith
  have a4 : y / 2 ≤ 2 * (J0 : ℝ) - 1 := by
    have : ⌈y⌉₊ ≤ 2 * J0 + 1 := by omega
    have : (⌈y⌉₊ : ℝ) ≤ ((2 * J0 + 1 : ℕ) : ℝ) := by exact_mod_cast this
    push_cast at this; linarith
  have hJ1p : (1 : ℝ) ≤ J1 := by exact_mod_cast le_trans hJ0pos hJ
  have b1 : alph * Real.log y ≤ Real.log (2 * (J1 : ℝ) + 1) := by
    rw [← hlogya]; exact Real.log_le_log hya a1
  have b2 : Real.log (2 * (J0 : ℝ) + 1) ≤ Real.log 2 + Real.log y := by
    rw [← Real.log_mul (by norm_num) hy0.ne']; exact Real.log_le_log (by positivity) a2
  have b3 : Real.log (2 * (J1 : ℝ) - 1) ≤ alph * Real.log y := by
    rw [← hlogya]; exact Real.log_le_log (by linarith) a3
  have b4 : Real.log y - Real.log 2 ≤ Real.log (2 * (J0 : ℝ) - 1) := by
    rw [← Real.log_div hy0.ne' (by norm_num)]; exact Real.log_le_log (by positivity) a4
  rw [abs_le]; constructor <;> linarith

end ZAsymp


section Item6e1
open Classical

/-! Tao Lemma 2.1 reindexing for Sec 5 (6e step (iii)).
Merge note: `Av` .. `Av_padv` below duplicate main draft lines 149-302; drop them on merge. -/

def Av (v : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => Av v k + v k

def Sv (v : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => 3 * Sv v k + 2 ^ Av v k

lemma AvSv_congr (v w : ℕ → ℕ) (k : ℕ) (h : ∀ i < k, v i = w i) :
    Av v k = Av w k ∧ Sv v k = Sv w k := by
  induction k with
  | zero => simp [Av, Sv]
  | succ k ih =>
    obtain ⟨h1, h2⟩ := ih (fun i hi => h i (by omega))
    have h3 := h k (by omega)
    simp only [Av, Sv, h1, h2, h3, and_self]

lemma A_S_eq (n k : ℕ) :
    A n k = Av (fun i => a (syracuseStep^[i] n)) k ∧
      S n k = Sv (fun i => a (syracuseStep^[i] n)) k := by
  induction k with
  | zero => simp [A, Av, S, Sv]
  | succ k ih =>
    obtain ⟨h1, h2⟩ := ih
    simp only [A, Av, S, Sv, h1, h2, and_self]

lemma factorization_two_pow_mul_odd (e m : ℕ) (hm : Odd m) :
    (2 ^ e * m).factorization 2 = e := by
  have hm0 : m ≠ 0 := by obtain ⟨r, hr⟩ := hm; omega
  have hnd : ¬ 2 ∣ m := by obtain ⟨r, hr⟩ := hm; omega
  rw [Nat.factorization_mul (pow_ne_zero _ two_ne_zero) hm0, Finsupp.add_apply,
    Nat.factorization_pow, Nat.factorization_eq_zero_of_not_dvd hnd]
  simp [Nat.prime_two.factorization_self]

lemma valuation_char_mpr (N : ℕ) (hN : Odd N) (v : ℕ → ℕ) (hv : ∀ i, 1 ≤ v i) (k : ℕ) :
    (∃ m, Odd m ∧ 2 ^ Av v k * m = 3 ^ k * N + Sv v k) →
      ∀ i < k, a (syracuseStep^[i] N) = v i := by
  induction k with
  | zero => intro _ i hi; omega
  | succ k ih =>
    rintro ⟨m, hm, hk⟩
    set P := 2 ^ Av v k with hP
    set X := 3 ^ k * N + Sv v k with hX
    have hkey : P * (2 ^ v k * m) = 3 * X + P := by
      rw [hP, hX, ← mul_assoc, ← pow_add]
      have : Av v (k + 1) = Av v k + v k := rfl
      rw [← this, hk]
      simp only [Sv, pow_succ]; ring
    have hdiv3 : P ∣ 3 * X := by
      have h1 : P ∣ 3 * X + P := ⟨_, hkey.symm⟩
      exact Nat.dvd_add_self_right.mp h1
    have hcop : Nat.Coprime P 3 := Nat.Coprime.pow_left _ (by norm_num)
    have hdivX : P ∣ X := hcop.dvd_of_dvd_mul_left hdiv3
    obtain ⟨Y, hY⟩ := hdivX
    have hPpos : 0 < P := by positivity
    have hY2 : 2 ^ v k * m = 3 * Y + 1 := by
      apply Nat.eq_of_mul_eq_mul_left hPpos
      rw [hkey, hY]; ring
    have hYodd : Odd Y := by
      obtain ⟨j, hj⟩ : ∃ j, v k = j + 1 := ⟨v k - 1, by have := hv k; omega⟩
      rw [hj, pow_succ] at hY2
      refine Nat.odd_iff.mpr ?_
      have : 2 ∣ 3 * Y + 1 := ⟨2 ^ j * m, by rw [← hY2]; ring⟩
      omega
    have hlow := ih ⟨Y, hYodd, by rw [← hY]⟩
    intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | hi
    · exact hlow i hi
    · subst hi
      obtain ⟨h1, h2⟩ := AvSv_congr (fun i => a (syracuseStep^[i] N)) v i hlow
      obtain ⟨h3, h4⟩ := A_S_eq N i
      have hf := iterate_formula N i
      rw [h3, h4, h1, h2, ← hX, hY] at hf
      have hSY : syracuseStep^[i] N = Y := Nat.eq_of_mul_eq_mul_left hPpos hf
      show (3 * syracuseStep^[i] N + 1).factorization 2 = v i
      rw [hSY, ← hY2]
      exact factorization_two_pow_mul_odd _ _ hm

lemma Av_eq_sum (v : ℕ → ℕ) (k : ℕ) : Av v k = ∑ i ∈ Finset.range k, v i := by
  induction k with
  | zero => simp [Av]
  | succ k ih => rw [Av, ih, Finset.sum_range_succ]

lemma Av_padv {n : ℕ} (w : Fin n → ℕ) : Av (padv w) n = absv w := by
  rw [Av_eq_sum, absv, ← Fin.sum_univ_eq_sum_range]
  exact Finset.sum_congr rfl (fun i _ => by simp [padv])

/-- Lemma 2.1, forward identity in tuple form: `3^k N + S(a⃗) = 2^{|a⃗|} Syr^k N`. -/
lemma key_fwd (N k : ℕ) :
    3 ^ k * N + Sv (padv (vecn k N)) k = 2 ^ absv (vecn k N) * syracuseStep^[k] N := by
  have hc : ∀ i < k, padv (vecn k N) i = a (syracuseStep^[i] N) := by
    intro i hi; simp [padv, vecn, hi]
  obtain ⟨h1, h2⟩ := AvSv_congr _ _ k hc
  obtain ⟨h3, h4⟩ := A_S_eq N k
  rw [← Av_padv (vecn k N), h1, h2, ← h3, ← h4]
  exact (iterate_formula N k).symm

/-- Lemma 2.1, backward direction in tuple form. -/
lemma key_bwd (N M k : ℕ) (hN : Odd N) (hM : Odd M) (v : Fin k → ℕ) (hv : ∀ i, 1 ≤ v i)
    (h : 3 ^ k * N + Sv (padv v) k = 2 ^ absv v * M) :
    vecn k N = v ∧ syracuseStep^[k] N = M := by
  have hp : ∀ i, 1 ≤ padv v i := by
    intro i; unfold padv; split_ifs <;> simp [hv]
  have hc := valuation_char_mpr N hN (padv v) hp k ⟨M, hM, by rw [Av_padv]; exact h.symm⟩
  have hvec : vecn k N = v := by
    funext i
    have := hc i i.isLt
    show a (syracuseStep^[(i : ℕ)] N) = v i
    rw [this]; simp [padv]
  refine ⟨hvec, ?_⟩
  have hf := key_fwd N k
  rw [hvec, h] at hf
  exact (Nat.eq_of_mul_eq_mul_left (by positivity) hf).symm

/-- The starting point `N_{a⃗,M} = (2^{|a⃗|} M - S(a⃗)) / 3^k`. -/
noncomputable def Nof (k : ℕ) (v : Fin k → ℕ) (M : ℕ) : ℕ := (2 ^ absv v * M - Sv (padv v) k) / 3 ^ k

lemma Nof_eq (N M k : ℕ) (v : Fin k → ℕ) (h : 3 ^ k * N + Sv (padv v) k = 2 ^ absv v * M) :
    Nof k v M = N := by
  unfold Nof
  rw [← h, Nat.add_sub_cancel]
  exact Nat.mul_div_cancel_left N (by positivity)

/-- 6e (iii): sum over `N_y` of an event in `(a⃗^{(k)}(N), Syr^k N)` reindexed by Lemma 2.1. -/
lemma reindex (y : ℝ) (k : ℕ) (AA : Finset (Fin k → ℕ)) (hAA : ∀ v ∈ AA, ∀ i, 1 ≤ v i)
    (MM : Finset ℕ) (hMM : ∀ M ∈ MM, Odd M) :
    ∑ N ∈ oddIcc y, (if vecn k N ∈ AA ∧ syracuseStep^[k] N ∈ MM then (1 : ℝ) / N else 0) =
    ∑ p ∈ AA ×ˢ MM, (if 3 ^ k * Nof k p.1 p.2 + Sv (padv p.1) k = 2 ^ absv p.1 * p.2 ∧
        Nof k p.1 p.2 ∈ oddIcc y then (1 : ℝ) / (Nof k p.1 p.2) else 0) := by
  have hodd : ∀ N ∈ oddIcc y, Odd N := fun N hN => (Finset.mem_filter.1 hN).2
  refine Finset.sum_bij_ne_zero (fun N _ _ => (vecn k N, syracuseStep^[k] N)) ?_ ?_ ?_ ?_
  · intro N _ hne
    have hc : vecn k N ∈ AA ∧ syracuseStep^[k] N ∈ MM := by
      by_contra hc; exact hne (if_neg hc)
    exact Finset.mem_product.2 hc
  · intro N1 _ _ N2 _ _ heq
    simp only [Prod.mk.injEq] at heq
    have e1 := key_fwd N1 k
    have e2 := key_fwd N2 k
    rw [heq.1, heq.2, ← e2] at e1
    exact Nat.eq_of_mul_eq_mul_left (by positivity) (Nat.add_right_cancel e1)
  · rintro ⟨v, M⟩ hp hne
    obtain ⟨hv, hM⟩ := Finset.mem_product.1 hp
    have hc : 3 ^ k * Nof k v M + Sv (padv v) k = 2 ^ absv v * M ∧ Nof k v M ∈ oddIcc y := by
      by_contra hc; exact hne (if_neg hc)
    obtain ⟨h1, h2⟩ := key_bwd _ M k (hodd _ hc.2) (hMM M hM) v (hAA v hv) hc.1
    refine ⟨Nof k v M, hc.2, ?_, ?_⟩
    · rw [if_pos ⟨by rw [h1]; exact hv, by rw [h2]; exact hM⟩]
      exact one_div_ne_zero (Nat.cast_ne_zero.2 (hodd _ hc.2).pos.ne')
    · simp [h1, h2]
  · intro N hN hne
    have hc : vecn k N ∈ AA ∧ syracuseStep^[k] N ∈ MM := by
      by_contra hc; exact hne (if_neg hc)
    have hfw := key_fwd N k
    have hN' := Nof_eq N _ k _ hfw
    dsimp only
    rw [hN', if_pos hc, if_pos ⟨hfw, hN⟩]

end Item6e1

section Item6e2
open Classical

/-- Disjoint indicators sum to the indicator of the union. -/
lemma ind_sum (I : Finset ℕ) (G : ℕ → ℕ → Prop) (N : ℕ) (w : ℝ)
    (hdisj : ∀ n ∈ I, ∀ n' ∈ I, G n N → G n' N → n = n') :
    ∑ n ∈ I, (if G n N then w else 0) = if (∃ n ∈ I, G n N) then w else 0 := by
  by_cases h : ∃ n ∈ I, G n N
  · obtain ⟨n, hn, hg⟩ := h
    rw [if_pos ⟨n, hn, hg⟩, Finset.sum_eq_single_of_mem n hn
      (fun n' hn' hne => if_neg (fun hg' => hne (hdisj n' hn' n hn hg' hg))), if_pos hg]
  · rw [if_neg h]
    exact Finset.sum_eq_zero (fun n hn => if_neg (fun hg => h ⟨n, hn, hg⟩))

/-- 6e (ii), abstract form: if `P` is the disjoint union of the `G n` on the good event, then
`|P_y(P) - Σ_n P_y(G n)| ≤ P_y(not good)`. -/
lemma prob_sum_disj (y : ℝ) (P good : ℕ → Prop) (G : ℕ → ℕ → Prop) (I : Finset ℕ)
    (hdisj : ∀ N ∈ oddIcc y, ∀ n ∈ I, ∀ n' ∈ I, G n N → G n' N → n = n')
    (hP : ∀ N ∈ oddIcc y, good N → (P N ↔ ∃ n ∈ I, G n N)) :
    |prob y P - ∑ n ∈ I, prob y (G n)| ≤ prob y (fun N => ¬ good N) := by
  have hZ := Z_nonneg y
  unfold prob
  rw [← Finset.sum_div, Finset.sum_comm, ← sub_div, ← Finset.sum_sub_distrib, abs_div,
    abs_of_nonneg hZ]
  gcongr
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun N hN => ?_)
  rw [ind_sum I (fun n N => G n N) N _ (hdisj N hN)]
  have hw : (0 : ℝ) ≤ 1 / (N : ℝ) := by positivity
  generalize (1 : ℝ) / N = w at hw ⊢
  by_cases hg : good N
  · rw [if_neg (not_not.2 hg)]
    by_cases hp : P N
    · rw [if_pos hp, if_pos ((hP N hN hg).1 hp)]; simp
    · rw [if_neg hp, if_neg (fun h => hp ((hP N hN hg).2 h))]; simp
  · rw [if_pos hg]
    split_ifs <;> simp [abs_of_nonneg hw, hw]

/-- First passage after a prefix that stays above `x`. -/
lemma T_shift (x : ℝ) (N k : ℕ) (hgt : ∀ j < k, x < (syracuseStep^[j] N : ℝ))
    (hR : Reaches x (syracuseStep^[k] N)) :
    Reaches x N ∧ T x N = k + T x (syracuseStep^[k] N) ∧
      Pass x N = Pass x (syracuseStep^[k] N) := by
  have hR' : Reaches x N :=
    ⟨T x (syracuseStep^[k] N) + k, by rw [← iter_comp]; exact T_spec x _ hR⟩
  have hle : T x N ≤ T x (syracuseStep^[k] N) + k :=
    T_le x N _ (by rw [← iter_comp]; exact T_spec x _ hR)
  have hge : k ≤ T x N := by
    by_contra h
    push_neg at h
    exact absurd (T_spec x N hR') (not_le.2 (hgt _ h))
  obtain ⟨i, hi⟩ : ∃ i, T x N = i + k := ⟨T x N - k, by omega⟩
  have hTi : T x (syracuseStep^[k] N) ≤ i :=
    T_le x _ i (by rw [iter_comp, ← hi]; exact T_spec x N hR')
  have hT : T x N = k + T x (syracuseStep^[k] N) := by omega
  refine ⟨hR', hT, ?_⟩
  unfold Pass
  rw [hT, add_comm, ← iter_comp]

/-- 6e (i): if the prefix of `N` up to `k` follows (5.14) and `Syr^k N ∈ E'`, then the first
passage of `N` is at `k + m0` and lands in `E`. Hence the events `G_n` are disjoint in `n`. -/
lemma Gn_event {x B W : ℝ} {N k m0 : ℕ} (E : ℕ → Prop) (hx : 0 < x) (hN : 1 ≤ N)
    (happ : ∀ j ≤ k, |Real.log (syracuseStep^[j] N : ℝ) - (Real.log N + j * Real.log (3 / 4))| ≤ B)
    (hWm : W + 2 * B < m0 * Real.log (4 / 3))
    (hM : Eprime x m0 W E (syracuseStep^[k] N)) :
    Reaches x N ∧ T x N = k + m0 ∧ E (Pass x N) := by
  obtain ⟨hR, hT, hE, hlog⟩ := hM
  have h43 : Real.log (3 / 4 : ℝ) = - Real.log (4 / 3) := by
    rw [show (3 / 4 : ℝ) = (4 / 3)⁻¹ by norm_num, Real.log_inv]
  have hL : 0 < Real.log (4 / 3 : ℝ) := Real.log_pos (by norm_num)
  have hgt : ∀ j < k, x < (syracuseStep^[j] N : ℝ) := by
    intro j hj
    have hpos : (0 : ℝ) < (syracuseStep^[j] N : ℝ) := by
      have := iter_one_le hN j; exact_mod_cast this
    have h1 := abs_le.1 (happ j hj.le)
    have h2 := abs_le.1 (happ k le_rfl)
    have h3 := abs_le.1 hlog
    rw [h43] at h1 h2
    have hjk : (j : ℝ) + 1 ≤ k := by exact_mod_cast hj
    have hkj : (j : ℝ) * Real.log (4 / 3) + Real.log (4 / 3) ≤ (k : ℝ) * Real.log (4 / 3) := by
      have := mul_le_mul_of_nonneg_right hjk hL.le
      linarith
    have : Real.log x < Real.log (syracuseStep^[j] N : ℝ) := by
      linarith [h1.1, h2.2, h3.1]
    exact (Real.log_lt_log_iff hx hpos).1 this
  obtain ⟨hR', hT', hP'⟩ := T_shift x N k hgt hR
  refine ⟨hR', by rw [hT', hT], ?_⟩
  rw [hP']; exact hE

end Item6e2


section Item6e3
open Classical

/-- Good valuation prefixes of length `k` (entries in `[1,K]`, deviation `≤ D`). -/
def AApred (D : ℝ) (k : ℕ) (v : Fin k → ℕ) : Prop :=
  ∀ j ∈ Finset.Icc 1 k, |(ps (padv v) j : ℝ) - 2 * j| ≤ D

noncomputable def AAk (D : ℝ) (K k : ℕ) : Finset (Fin k → ℕ) := (Box k K).filter (AApred D k)

/-- Tao's `E'` restricted to deviation-good `M` (our `E''`), as a finset. -/
def MMpred (x W D : ℝ) (m0 : ℕ) (E : ℕ → Prop) (M : ℕ) : Prop :=
  Odd M ∧ Eprime x m0 W E M ∧ ∀ j ∈ Finset.Icc 1 m0, |(A M j : ℝ) - 2 * j| ≤ 2 * D

noncomputable def MMs (x W D : ℝ) (m0 Mmax : ℕ) (E : ℕ → Prop) : Finset ℕ :=
  (Finset.range Mmax).filter (MMpred x W D m0 E)

/-- The event `G_n`: good prefix up to `n - m0`, then `Syr^{n-m0} N ∈ E''`. -/
def Gev (x W D : ℝ) (m0 K Mmax : ℕ) (E : ℕ → Prop) (n N : ℕ) : Prop :=
  vecn (n - m0) N ∈ AAk D K (n - m0) ∧ syracuseStep^[n - m0] N ∈ MMs x W D m0 Mmax E

lemma Gev_pass {x W D : ℝ} {m0 K Mmax n N : ℕ} (E : ℕ → Prop) (hx : 0 < x) (hN : 1 ≤ N)
    (hD : 0 ≤ D) (h4 : (4 : ℝ) ^ (n - m0) ≤ N) (hmn : m0 ≤ n)
    (hWm : W + 2 * ((2 * D + 1) * Real.log 2) < m0 * Real.log (4 / 3))
    (hG : Gev x W D m0 K Mmax E n N) :
    Reaches x N ∧ T x N = n ∧ E (Pass x N) := by
  obtain ⟨hv, hM⟩ := hG
  have hdevv := (Finset.mem_filter.1 hv).2
  obtain ⟨_, hE', _⟩ := (Finset.mem_filter.1 hM).2
  have happ : ∀ j ≤ n - m0, |Real.log (syracuseStep^[j] N : ℝ) -
      (Real.log N + j * Real.log (3 / 4))| ≤ (2 * D + 1) * Real.log 2 := by
    intro j hj
    apply log_syr_approx N j D hD (le_trans (pow_le_pow_right₀ (by norm_num) hj) h4)
    rcases Nat.eq_zero_or_pos j with h0 | hpos
    · subst h0; simpa [A] using hD
    · have := hdevv j (Finset.mem_Icc.2 ⟨hpos, hj⟩)
      rwa [ps_padv_vecn (n - m0) N j hj] at this
  obtain ⟨hR, hT, hE⟩ := Gn_event E hx hN happ hWm hE'
  exact ⟨hR, by rw [hT]; omega, hE⟩

lemma Gev_disj {x W D : ℝ} {m0 n0 K Mmax N : ℕ} (E : ℕ → Prop) (hx : 0 < x) (hN : 1 ≤ N)
    (hD : 0 ≤ D) (h4 : (4 : ℝ) ^ n0 ≤ N)
    (hWm : W + 2 * ((2 * D + 1) * Real.log 2) < m0 * Real.log (4 / 3)) :
    ∀ n ∈ Finset.Icc m0 n0, ∀ n' ∈ Finset.Icc m0 n0,
      Gev x W D m0 K Mmax E n N → Gev x W D m0 K Mmax E n' N → n = n' := by
  intro n hn n' hn' hG hG'
  have h1 := Finset.mem_Icc.1 hn
  have h2 := Finset.mem_Icc.1 hn'
  have e1 := (Gev_pass E hx hN hD
    (le_trans (pow_le_pow_right₀ (by norm_num) (by omega)) h4) h1.1 hWm hG).2.1
  have e2 := (Gev_pass E hx hN hD
    (le_trans (pow_le_pow_right₀ (by norm_num) (by omega)) h4) h2.1 hWm hG').2.1
  omega

lemma Gev_of_good {x W D : ℝ} {m0 n0 K Mmax n N : ℕ} (E : ℕ → Prop) (hx : 0 < x) (hNo : Odd N)
    (hD : 0 ≤ D) (h4 : (4 : ℝ) ^ n0 ≤ N) (hm0 : 1 ≤ m0) (hmn : m0 ≤ n) (hn0 : n ≤ n0)
    (hW : 2 * ((2 * D + 1) * Real.log 2) + Real.log (4 / 3) ≤ W)
    (hWm : W + 2 * ((2 * D + 1) * Real.log 2) < m0 * Real.log (4 / 3))
    (hK : 2 * (n0 : ℝ) + D ≤ K)
    (hMmax : Real.exp (Real.log x + m0 * Real.log (4 / 3) + W) < Mmax)
    (hgood : ∀ j ∈ Finset.Icc 1 n0, |(A N j : ℝ) - 2 * j| ≤ D)
    (hR : Reaches x N) (hT : T x N = n) (hE : E (Pass x N)) :
    Gev x W D m0 K Mmax E n N := by
  have hN : 1 ≤ N := hNo.pos
  have happ := approx_all N n0 D hD h4 hgood
  have hE' := (event_iff E hx hN happ hm0 hmn hn0 hW hWm).1 ⟨hR, hT, hE⟩
  have hA0 : ∀ i, i ≤ n0 → |(A N i : ℝ) - 2 * i| ≤ D := by
    intro i hi
    rcases Nat.eq_zero_or_pos i with h0 | hpos
    · subst h0; simpa [A] using hD
    · exact hgood i (Finset.mem_Icc.2 ⟨hpos, hi⟩)
  refine ⟨Finset.mem_filter.2 ⟨?_, ?_⟩, Finset.mem_filter.2 ⟨?_, ?_⟩⟩
  · rw [Box, Fintype.mem_piFinset]
    intro i
    have hi : (i : ℕ) < n - m0 := i.isLt
    have hodd : Odd (syracuseStep^[(i : ℕ)] N) := by
      rcases Nat.eq_zero_or_pos (i : ℕ) with h0 | hpos
      · rw [h0]; simpa using hNo
      · exact iter_odd N i hpos
    refine Finset.mem_Icc.2 ⟨a_pos_of_odd hodd, ?_⟩
    have h1 := abs_le.1 (hA0 ((i : ℕ) + 1) (by omega))
    have hAs : A N ((i : ℕ) + 1) = A N i + a (syracuseStep^[(i : ℕ)] N) := rfl
    have hle : (a (syracuseStep^[(i : ℕ)] N) : ℝ) ≤ K := by
      have h2 : (a (syracuseStep^[(i : ℕ)] N) : ℝ) ≤ A N ((i : ℕ) + 1) := by
        rw [hAs]; push_cast; linarith [(Nat.cast_nonneg (A N i) : (0 : ℝ) ≤ _)]
      have hi' : ((i : ℕ) : ℝ) + 1 ≤ n0 := by exact_mod_cast (show (i : ℕ) + 1 ≤ n0 by omega)
      push_cast at h1
      linarith [h1.2]
    exact_mod_cast hle
  · intro j hj
    have hj' := Finset.mem_Icc.1 hj
    rw [ps_padv_vecn (n - m0) N j hj'.2]
    exact hA0 j (by omega)
  · rw [Finset.mem_range]
    obtain ⟨_, _, _, hlog⟩ := hE'
    have hlog2 := (abs_le.1 hlog).2
    have hpos : (0 : ℝ) < (syracuseStep^[n - m0] N : ℝ) := by
      have := iter_one_le hN (n - m0); exact_mod_cast this
    have : (syracuseStep^[n - m0] N : ℝ) < Mmax := by
      calc (syracuseStep^[n - m0] N : ℝ) = Real.exp (Real.log (syracuseStep^[n - m0] N : ℝ)) :=
            (Real.exp_log hpos).symm
        _ ≤ Real.exp (Real.log x + m0 * Real.log (4 / 3) + W) := Real.exp_le_exp.2 (by linarith)
        _ < Mmax := hMmax
    exact_mod_cast this
  · unfold MMpred
    refine ⟨?_, hE', ?_⟩
    · rcases Nat.eq_zero_or_pos (n - m0) with h0 | hpos
      · rw [h0]; simpa using hNo
      · exact iter_odd N _ hpos
    · intro j hj
      have hj' := Finset.mem_Icc.1 hj
      exact dev_shift N (n - m0) n0 D hD hgood j (by omega)

/-- 6e (i)+(ii) combined: on the deviation-good event, with first passage in `[m0, n0]`,
`Reaches ∧ E(Pass)` is the disjoint union of the `G_n`, `m0 ≤ n ≤ n0`. -/
lemma Gev_iff {x W D : ℝ} {m0 n0 K Mmax N : ℕ} (E : ℕ → Prop) (hx : 0 < x) (hNo : Odd N)
    (hD : 0 ≤ D) (h4 : (4 : ℝ) ^ n0 ≤ N) (hm0 : 1 ≤ m0)
    (hW : 2 * ((2 * D + 1) * Real.log 2) + Real.log (4 / 3) ≤ W)
    (hWm : W + 2 * ((2 * D + 1) * Real.log 2) < m0 * Real.log (4 / 3))
    (hK : 2 * (n0 : ℝ) + D ≤ K)
    (hMmax : Real.exp (Real.log x + m0 * Real.log (4 / 3) + W) < Mmax)
    (hgood : ∀ j ∈ Finset.Icc 1 n0, |(A N j : ℝ) - 2 * j| ≤ D)
    (hTr : Reaches x N → m0 ≤ T x N ∧ T x N ≤ n0) :
    (Reaches x N ∧ E (Pass x N)) ↔ ∃ n ∈ Finset.Icc m0 n0, Gev x W D m0 K Mmax E n N := by
  constructor
  · rintro ⟨hR, hE⟩
    obtain ⟨h1, h2⟩ := hTr hR
    exact ⟨T x N, Finset.mem_Icc.2 ⟨h1, h2⟩,
      Gev_of_good E hx hNo hD h4 hm0 h1 h2 hW hWm hK hMmax hgood hR rfl hE⟩
  · rintro ⟨n, hn, hG⟩
    have h1 := Finset.mem_Icc.1 hn
    obtain ⟨hR, _, hE⟩ := Gev_pass E hx hNo.pos hD
      (le_trans (pow_le_pow_right₀ (by norm_num) (by omega)) h4) h1.1 hWm hG
    exact ⟨hR, hE⟩

end Item6e3

section Item6e4
open Classical

/-- 6e (iii) applied to `G_n`. -/
lemma prob_Gev (y x W D : ℝ) (m0 K Mmax : ℕ) (E : ℕ → Prop) (n : ℕ) :
    prob y (Gev x W D m0 K Mmax E n) =
      (∑ p ∈ AAk D K (n - m0) ×ˢ MMs x W D m0 Mmax E,
        (if 3 ^ (n - m0) * Nof (n - m0) p.1 p.2 + Sv (padv p.1) (n - m0) = 2 ^ absv p.1 * p.2 ∧
          Nof (n - m0) p.1 p.2 ∈ oddIcc y then (1 : ℝ) / (Nof (n - m0) p.1 p.2) else 0)) / Z y := by
  have hAA : ∀ v ∈ AAk D K (n - m0), ∀ i, 1 ≤ v i := fun v hv i =>
    (Finset.mem_Icc.1 (Fintype.mem_piFinset.1 (Finset.mem_filter.1 hv).1 i)).1
  have hMM : ∀ M ∈ MMs x W D m0 Mmax E, Odd M := fun M hM => by
    obtain ⟨h, _⟩ := (Finset.mem_filter.1 hM).2; exact h
  rw [← reindex y (n - m0) _ hAA _ hMM]
  unfold prob
  congr 1
  refine Finset.sum_congr rfl (fun N _ => ?_)
  by_cases hg : Gev x W D m0 K Mmax E n N
  · have hg' : vecn (n - m0) N ∈ AAk D K (n - m0) ∧
        syracuseStep^[n - m0] N ∈ MMs x W D m0 Mmax E := hg
    rw [if_pos hg, if_pos hg']
  · have hg' : ¬ (vecn (n - m0) N ∈ AAk D K (n - m0) ∧
        syracuseStep^[n - m0] N ∈ MMs x W D m0 Mmax E) := hg
    rw [if_neg hg, if_neg hg']

/-- 6e (i)-(ii) in probability: `P_y(Reaches ∧ E(Pass))` is `Σ_{n=m0}^{n0} P_y(G_n)` up to
the probability of the deviation-bad or passage-out-of-range event. -/
lemma sec5_split (y : ℝ) {x W D : ℝ} {m0 n0 K Mmax : ℕ} (E : ℕ → Prop) (hx : 0 < x)
    (hD : 0 ≤ D) (hm0 : 1 ≤ m0)
    (hW : 2 * ((2 * D + 1) * Real.log 2) + Real.log (4 / 3) ≤ W)
    (hWm : W + 2 * ((2 * D + 1) * Real.log 2) < m0 * Real.log (4 / 3))
    (hK : 2 * (n0 : ℝ) + D ≤ K)
    (hMmax : Real.exp (Real.log x + m0 * Real.log (4 / 3) + W) < Mmax)
    (h4 : (4 : ℝ) ^ n0 ≤ y) :
    |prob y (fun N => Reaches x N ∧ E (Pass x N)) -
        ∑ n ∈ Finset.Icc m0 n0, prob y (Gev x W D m0 K Mmax E n)| ≤
      prob y (fun N => ¬ ((∀ j ∈ Finset.Icc 1 n0, |(A N j : ℝ) - 2 * j| ≤ D) ∧
        (Reaches x N → m0 ≤ T x N ∧ T x N ≤ n0))) := by
  have hmem : ∀ N ∈ oddIcc y, Odd N ∧ (4 : ℝ) ^ n0 ≤ N := fun N hN => by
    obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hN
    exact ⟨h2, le_trans h4 (le_trans (Nat.le_ceil y) (by exact_mod_cast (Finset.mem_Icc.1 h1).1))⟩
  refine prob_sum_disj y _ _ _ _ ?_ ?_
  · intro N hN
    exact Gev_disj E hx (hmem N hN).1.pos hD (hmem N hN).2 hWm
  · intro N hN hg
    exact Gev_iff E hx (hmem N hN).1 hD (hmem N hN).2 hm0 hW hWm hK hMmax hg.1 hg.2

end Item6e4


/-! ===== merged from _6e5/_6f (S21) ===== -/







def Fnat (a : ℕ → ℕ) (n : ℕ) : ℕ := ∑ j ∈ Finset.range n, 3 ^ j * 2 ^ (ps a n - ps a (j + 1))

noncomputable def syrZ (n : ℕ) (a : ℕ → ℕ) : ZMod (3 ^ n) :=
  (Fnat a n : ZMod (3 ^ n)) * ((2 : ZMod (3 ^ n))⁻¹) ^ ps a n

lemma two_mul_inv (n : ℕ) : (2 : ZMod (3 ^ n)) * (2 : ZMod (3 ^ n))⁻¹ = 1 := by
  have hc : Nat.Coprime 2 (3 ^ n) := Nat.Coprime.pow_right _ (by norm_num)
  have := ZMod.coe_mul_inv_eq_one (n := 3 ^ n) 2 hc
  simpa using this



section Item6e5
open Classical

lemma ps_eq_Av (v : ℕ → ℕ) : ∀ k, ps v k = Av v k
  | 0 => rfl
  | k + 1 => by rw [ps, Av, ps_eq_Av v k]

lemma padv_pos {k : ℕ} (v : Fin k → ℕ) (hv : ∀ i, 1 ≤ v i) : ∀ i, 1 ≤ padv v i := fun i => by
  unfold padv; split_ifs <;> simp [hv]

lemma Av_ge (v : ℕ → ℕ) (hv : ∀ i, 1 ≤ v i) : ∀ k, k ≤ Av v k
  | 0 => by simp [Av]
  | k + 1 => by have := Av_ge v hv k; have := hv k; simp only [Av]; omega

lemma Sv_le (v : ℕ → ℕ) (hv : ∀ i, 1 ≤ v i) : ∀ k, (Sv v k : ℝ) ≤ 2 ^ Av v k * ((3 / 2 : ℝ) ^ k - 1)
  | 0 => by simp [Sv, Av]
  | k + 1 => by
    have ih := Sv_le v hv k
    have h1 : (2 : ℝ) ^ (Av v k + 1) ≤ 2 ^ Av v (k + 1) := by
      rw [Av]; exact pow_le_pow_right₀ (by norm_num) (by have := hv k; omega)
    have hp : (1 : ℝ) ≤ (3 / 2) ^ (k + 1) := one_le_pow₀ (by norm_num)
    rw [Sv]; push_cast
    calc 3 * (Sv v k : ℝ) + 2 ^ Av v k ≤ 3 * (2 ^ Av v k * ((3 / 2) ^ k - 1)) + 2 ^ Av v k := by
          linarith
      _ = 2 ^ (Av v k + 1) * ((3 / 2) ^ (k + 1) - 1) := by ring
      _ ≤ 2 ^ Av v (k + 1) * ((3 / 2) ^ (k + 1) - 1) :=
          mul_le_mul_of_nonneg_right h1 (by linarith)

lemma Sv_odd (v : ℕ → ℕ) (hv : ∀ i, 1 ≤ v i) : ∀ k, 1 ≤ k → Odd (Sv v k)
  | 0, h => absurd h (by norm_num)
  | 1, _ => by simp [Sv, Av]
  | k + 2, _ => by
    have ih := Sv_odd v hv (k + 1) (by omega)
    have hA : 1 ≤ Av v (k + 1) := le_trans (by omega) (Av_ge v hv (k + 1))
    rw [Sv]
    have he : Even (2 ^ Av v (k + 1)) := Nat.even_pow.2 ⟨even_two, by omega⟩
    exact (Odd.mul ⟨1, by norm_num⟩ ih).add_even he

/-- The Lemma 2.1 preimage is automatically odd. -/
lemma cong_odd {k : ℕ} (hk : 1 ≤ k) (v : Fin k → ℕ) (hv : ∀ i, 1 ≤ v i) {N M : ℕ}
    (h : 3 ^ k * N + Sv (padv v) k = 2 ^ absv v * M) : Odd N := by
  have hab : 1 ≤ absv v := by
    rw [← Av_padv]; exact le_trans hk (Av_ge _ (padv_pos v hv) k)
  have hE : Even (2 ^ absv v * M) := (Nat.even_pow.2 ⟨even_two, by omega⟩).mul_right M
  rw [← h] at hE
  have hS := Sv_odd (padv v) (padv_pos v hv) k hk
  rcases Nat.even_or_odd N with hN | hN
  · exfalso
    have : Odd (3 ^ k * N + Sv (padv v) k) := (hN.mul_left _).add_odd hS
    exact (Nat.not_even_iff_odd.2 this) hE
  · exact hN

lemma Sv_padv_le {k : ℕ} (v : Fin k → ℕ) (hv : ∀ i, 1 ≤ v i) :
    (Sv (padv v) k : ℝ) ≤ 2 ^ absv v * ((3 / 2 : ℝ) ^ k - 1) := by
  have := Sv_le (padv v) (padv_pos v hv) k
  rwa [Av_padv] at this

/-- 6e (iv)/(v) core: size of `N_{v,M}` and the approximation `1/N ≈ 3^k 2^{-|v|} / M`. -/
lemma nof_approx (k : ℕ) (v : Fin k → ℕ) (hv : ∀ i, 1 ≤ v i) (M N : ℕ) (hN : 0 < N)
    (h : 3 ^ k * N + Sv (padv v) k = 2 ^ absv v * M) (hM : 2 * (3 / 2 : ℝ) ^ k ≤ M) :
    (3 : ℝ) ^ k * N ≤ 2 ^ absv v * M ∧ (2 : ℝ) ^ absv v * M ≤ 2 * 3 ^ k * N ∧
    0 ≤ (1 : ℝ) / N - 3 ^ k / (2 ^ absv v * M) ∧
    (1 : ℝ) / N - 3 ^ k / (2 ^ absv v * M) ≤
      2 * ((3 / 2 : ℝ) ^ k / M) * (3 ^ k / (2 ^ absv v * M)) := by
  have hS := Sv_padv_le v hv
  have hreal : (3 : ℝ) ^ k * N + Sv (padv v) k = 2 ^ absv v * M := by exact_mod_cast h
  set s : ℝ := (Sv (padv v) k : ℝ) with hs
  set P : ℝ := 2 ^ absv v with hP
  set c : ℝ := (3 / 2 : ℝ) ^ k with hc
  have hs0 : 0 ≤ s := by rw [hs]; positivity
  have hP0 : 0 < P := by rw [hP]; positivity
  have hc1 : 1 ≤ c := one_le_pow₀ (by norm_num)
  have hM0 : (0 : ℝ) < M := by linarith
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have h3 : (0 : ℝ) < 3 ^ k := by positivity
  have h1 : (3 : ℝ) ^ k * N ≤ P * M := by linarith
  have hsc : s ≤ P * c := by (first | linarith | nlinarith)
  have hPc : P * c ≤ P * M / 2 := by
    have := mul_le_mul_of_nonneg_left hM hP0.le; (first | linarith | nlinarith)
  have h2 : P * M ≤ 2 * 3 ^ k * N := by linarith
  have hQ : 0 < P * M := by positivity
  have key : (1 : ℝ) / N - 3 ^ k / (P * M) = s / (N * (P * M)) := by
    rw [div_sub_div _ _ hN0.ne' hQ.ne']
    congr 1
    linarith
  refine ⟨h1, h2, ?_, ?_⟩
  · rw [key]; positivity
  · rw [key, div_le_iff₀ (by positivity)]
    have e : 2 * (c / M) * (3 ^ k / (P * M)) * (N * (P * M)) = 2 * c * 3 ^ k * N / M := by
      field_simp
    rw [e, le_div_iff₀ hM0]
    have hcM : s * M ≤ P * c * M := mul_le_mul_of_nonneg_right hsc hM0.le
    have : P * c * M = c * (P * M) := by ring
    (first | linarith [mul_le_mul_of_nonneg_left h2 (by linarith : (0 : ℝ) ≤ c)] | nlinarith [mul_le_mul_of_nonneg_left h2 (by linarith : (0 : ℝ) ≤ c)])

/-- Reversal of a tuple. -/
def revv {k : ℕ} (v : Fin k → ℕ) : Fin k → ℕ := fun i => v (Fin.rev i)

lemma absv_revv {k : ℕ} (v : Fin k → ℕ) : absv (revv v) = absv v := by
  unfold absv revv
  exact Fintype.sum_equiv Fin.revPerm _ _ (fun i => rfl)

lemma revv_pos {k : ℕ} (v : Fin k → ℕ) (hv : ∀ i, 1 ≤ v i) : ∀ i, 1 ≤ revv v i := fun i => hv _

lemma ps_rev_add {k : ℕ} (v : Fin k → ℕ) :
    ∀ m, m ≤ k → ps (padv (revv v)) m + Av (padv v) (k - m) = absv v
  | 0, _ => by simp [ps, Av_padv]
  | m + 1, hm => by
    have ih := ps_rev_add v m (by omega)
    have e : k - m = (k - (m + 1)) + 1 := by omega
    rw [e, Av] at ih
    have h1 : padv (revv v) m = v ⟨k - 1 - m, by omega⟩ := by
      simp only [padv, revv, dif_pos (show m < k by omega)]
      congr 1; ext; simp [Fin.rev]; omega
    have h2 : padv v (k - (m + 1)) = v ⟨k - 1 - m, by omega⟩ := by
      simp only [padv, dif_pos (show k - (m + 1) < k by omega)]
      congr 1; ext; simp; omega
    rw [ps, h1]
    rw [h2] at ih
    omega

lemma Sv_eq_sum (v : ℕ → ℕ) (k : ℕ) :
    Sv v k = ∑ i ∈ Finset.range k, 3 ^ (k - 1 - i) * 2 ^ Av v i := by
  induction k with
  | zero => simp [Sv]
  | succ k ih =>
    rw [Sv, ih, Finset.sum_range_succ, Finset.mul_sum]
    congr 1
    · apply Finset.sum_congr rfl
      intro i hi
      have hi' : i < k := Finset.mem_range.mp hi
      have : k + 1 - 1 - i = (k - 1 - i) + 1 := by omega
      rw [this, pow_succ]; ring
    · simp

/-- Tao's Syracuse variable uses the reversed tuple: `Fnat (rev v) = S(v)`. -/
lemma Fnat_rev {k : ℕ} (v : Fin k → ℕ) : Fnat (padv (revv v)) k = Sv (padv v) k := by
  have hk : ps (padv (revv v)) k = absv v := by
    have := ps_rev_add v k le_rfl; simp [Av] at this; exact this
  rw [Fnat, Sv_eq_sum, ← Finset.sum_range_reflect]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' : j < k := Finset.mem_range.mp hj
  have hp := ps_rev_add v (k - 1 - j + 1) (by omega)
  have e1 : k - (k - 1 - j + 1) = j := by omega
  have e2 : k - 1 - (k - 1 - j) = j := by omega
  rw [e1] at hp
  rw [hk]
  congr 2
  omega

lemma syrZ_rev {k : ℕ} (v : Fin k → ℕ) :
    syrZ k (padv (revv v)) = (Sv (padv v) k : ZMod (3 ^ k)) * ((2 : ZMod (3 ^ k))⁻¹) ^ absv v := by
  have hk : ps (padv (revv v)) k = absv v := by
    have := ps_rev_add v k le_rfl; simp [Av] at this; exact this
  rw [syrZ, Fnat_rev, hk]

/-- The Lemma 2.1 congruence in `ZMod 3^k` form. -/
lemma cong_iff {k : ℕ} (v : Fin k → ℕ) (M : ℕ) (hle : Sv (padv v) k ≤ 2 ^ absv v * M) :
    3 ^ k * Nof k v M + Sv (padv v) k = 2 ^ absv v * M ↔
      (M : ZMod (3 ^ k)) = syrZ k (padv (revv v)) := by
  rw [syrZ_rev]
  have hinv : (2 : ZMod (3 ^ k))⁻¹ * 2 = 1 := by rw [mul_comm]; exact two_mul_inv k
  constructor
  · intro h
    have h' := congrArg (fun n : ℕ => (n : ZMod (3 ^ k))) h
    push_cast at h'
    have h3 : ((3 : ZMod (3 ^ k))) ^ k = 0 := by exact_mod_cast ZMod.natCast_self (3 ^ k)
    rw [h3, zero_mul, zero_add] at h'
    rw [h']
    calc (M : ZMod (3 ^ k)) = ((2 : ZMod (3 ^ k))⁻¹ * 2) ^ absv v * M := by
          rw [hinv, one_pow, one_mul]
      _ = (2 : ZMod (3 ^ k)) ^ absv v * M * (2⁻¹) ^ absv v := by ring
  · intro h
    have h2 : ((2 : ZMod (3 ^ k))) ^ absv v * (M : ZMod (3 ^ k)) = Sv (padv v) k := by
      rw [h]
      calc (2 : ZMod (3 ^ k)) ^ absv v * ((Sv (padv v) k : ZMod (3 ^ k)) * 2⁻¹ ^ absv v)
          = (Sv (padv v) k : ZMod (3 ^ k)) * (2 * 2⁻¹) ^ absv v := by ring
        _ = Sv (padv v) k := by rw [two_mul_inv, one_pow, mul_one]
    have hz : ((2 ^ absv v * M - Sv (padv v) k : ℕ) : ZMod (3 ^ k)) = 0 := by
      rw [Nat.cast_sub hle]; push_cast; rw [h2, sub_self]
    have hd : 3 ^ k ∣ 2 ^ absv v * M - Sv (padv v) k := (ZMod.natCast_eq_zero_iff _ _).1 hz
    unfold Nof
    rw [Nat.mul_div_cancel' hd]
    omega

/-! ### S19 batch 2: from the Lemma 2.1 sum to `mu` and the `Osc` transfer (6e (v)). -/


noncomputable def mu (n K : ℕ) (Y : ZMod (3 ^ n)) : ℝ :=
  ∑ w ∈ (Box n K).filter (fun w => syrZ n (padv w) = Y), ((1 : ℝ) / 2) ^ (∑ i, w i)

noncomputable def Osc (m n : ℕ) (c : ZMod (3 ^ n) → ℝ) : ℝ :=
  ∑ Y : ZMod (3 ^ n), |c Y - (3 : ℝ) ^ m / 3 ^ n *
    ∑ Y' ∈ Finset.univ.filter (fun Y' : ZMod (3 ^ n) => Y'.val % 3 ^ m = Y.val % 3 ^ m), c Y'|

lemma revv_revv {k : ℕ} (v : Fin k → ℕ) : revv (revv v) = v := by
  funext i; simp [revv]

lemma revv_mem_Box {k K : ℕ} (v : Fin k → ℕ) (hv : v ∈ Box k K) : revv v ∈ Box k K := by
  unfold Box at *
  rw [Fintype.mem_piFinset] at *
  exact fun i => hv _

lemma rev_box_sum (k K : ℕ) (g : (Fin k → ℕ) → ℝ) :
    ∑ v ∈ Box k K, g (revv v) = ∑ w ∈ Box k K, g w :=
  Finset.sum_nbij' revv revv (fun v hv => revv_mem_Box v hv) (fun v hv => revv_mem_Box v hv)
    (fun v _ => revv_revv v) (fun v _ => revv_revv v) (fun _ _ => rfl)

/-- 6e (v) step 1: the Lemma 2.1 sum with `1/N` replaced by `3^k 2^{-|v|}/M` is a `v`-weighted
residue-class harmonic sum. -/
lemma sumq_eq (k : ℕ) (AA : Finset (Fin k → ℕ)) (hAA : ∀ v ∈ AA, ∀ i, 1 ≤ v i)
    (MM : Finset ℕ) (hMM : ∀ M ∈ MM, (3 / 2 : ℝ) ^ k ≤ M) :
    ∑ p ∈ AA ×ˢ MM, (if 3 ^ k * Nof k p.1 p.2 + Sv (padv p.1) k = 2 ^ absv p.1 * p.2 then
        (3 : ℝ) ^ k / (2 ^ absv p.1 * p.2) else 0) =
      ∑ v ∈ AA, ((1 : ℝ) / 2) ^ absv v *
        ∑ M ∈ MM.filter (fun M : ℕ => (M : ZMod (3 ^ k)) = syrZ k (padv (revv v))), (3 : ℝ) ^ k / M := by
  rw [Finset.sum_product]
  refine Finset.sum_congr rfl (fun v hv => ?_)
  rw [Finset.sum_filter, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun M hM => ?_)
  have hle : Sv (padv v) k ≤ 2 ^ absv v * M := by
    have h1 := Sv_padv_le v (hAA v hv)
    have h2 := hMM M hM
    have h3 : (0 : ℝ) ≤ 2 ^ absv v := by positivity
    have : (Sv (padv v) k : ℝ) ≤ 2 ^ absv v * M := by (first | linarith | nlinarith)
    exact_mod_cast this
  by_cases hc : 3 ^ k * Nof k v M + Sv (padv v) k = 2 ^ absv v * M
  · have hz := (cong_iff v M hle).1 hc
    rw [if_pos hc, if_pos hz]
    rw [one_div, inv_pow]
    field_simp
  · have hz : ¬ (M : ZMod (3 ^ k)) = syrZ k (padv (revv v)) := fun h => hc ((cong_iff v M hle).2 h)
    rw [if_neg hc, if_neg hz, mul_zero]

/-- 6e (v) step 2: over the full box the `v`-sum is `mu`. -/
lemma sumBox_eq_mu (k K : ℕ) (MM : Finset ℕ) :
    ∑ v ∈ Box k K, ((1 : ℝ) / 2) ^ absv v *
        ∑ M ∈ MM.filter (fun M : ℕ => (M : ZMod (3 ^ k)) = syrZ k (padv (revv v))), (3 : ℝ) ^ k / M =
      ∑ M ∈ MM, (3 : ℝ) ^ k / M * mu k K (M : ZMod (3 ^ k)) := by
  have e1 : ∀ v ∈ Box k K, ((1 : ℝ) / 2) ^ absv v *
      ∑ M ∈ MM.filter (fun M : ℕ => (M : ZMod (3 ^ k)) = syrZ k (padv (revv v))), (3 : ℝ) ^ k / M =
      ∑ M ∈ MM, (3 : ℝ) ^ k / M *
        (if syrZ k (padv (revv v)) = (M : ZMod (3 ^ k)) then ((1 : ℝ) / 2) ^ absv (revv v) else 0) := by
    intro v _
    rw [Finset.sum_filter, Finset.mul_sum, absv_revv]
    refine Finset.sum_congr rfl (fun M _ => ?_)
    by_cases h : (M : ZMod (3 ^ k)) = syrZ k (padv (revv v))
    · rw [if_pos h, if_pos h.symm]; ring
    · rw [if_neg h, if_neg (fun h' => h h'.symm)]; ring
  rw [Finset.sum_congr rfl e1, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun M _ => ?_)
  rw [← Finset.mul_sum]
  congr 1
  rw [rev_box_sum k K (fun w => if syrZ k (padv w) = (M : ZMod (3 ^ k)) then
      ((1 : ℝ) / 2) ^ absv w else 0), mu, Finset.sum_filter]
  rfl

/-- 6e (v) step 3 (generic): a bounded nonnegative test function sees `c` and its
`3^m`-average up to `H · Osc`. -/
lemma osc_transfer (m n : ℕ) (c h : ZMod (3 ^ n) → ℝ) (H : ℝ)
    (h0 : ∀ Y, 0 ≤ h Y) (hH : ∀ Y, h Y ≤ H) :
    |∑ Y, c Y * h Y - ∑ Y, ((3 : ℝ) ^ m / 3 ^ n *
        ∑ Y' ∈ Finset.univ.filter (fun Y' : ZMod (3 ^ n) => Y'.val % 3 ^ m = Y.val % 3 ^ m), c Y') *
          h Y| ≤ H * Osc m n c := by
  rw [← Finset.sum_sub_distrib, Osc, Finset.mul_sum]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum (fun Y _ => ?_))
  rw [← sub_mul, abs_mul, abs_of_nonneg (h0 Y), mul_comm]
  exact mul_le_mul_of_nonneg_right (hH Y) (abs_nonneg _)

lemma fiber_aux {n : ℕ} (MM : Finset ℕ) (g : ZMod (3 ^ n) → ℝ) (f : ℕ → ℝ) :
    ∑ Y, g Y * ∑ M ∈ MM.filter (fun M : ℕ => (M : ZMod (3 ^ n)) = Y), f M =
      ∑ M ∈ MM, g (M : ZMod (3 ^ n)) * f M := by
  simp_rw [Finset.sum_filter, Finset.mul_sum, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun M _ => ?_)
  rw [Finset.sum_ite_eq]
  simp

/-- 6e (v) step 4: the averaged term only sees `M mod 3^m`. -/
lemma fiber_sum (m n : ℕ) (hmn : m ≤ n) (c : ZMod (3 ^ n) → ℝ) (MM : Finset ℕ) :
    ∑ Y, ((3 : ℝ) ^ m / 3 ^ n *
        ∑ Y' ∈ Finset.univ.filter (fun Y' : ZMod (3 ^ n) => Y'.val % 3 ^ m = Y.val % 3 ^ m), c Y') *
          ∑ M ∈ MM.filter (fun M : ℕ => (M : ZMod (3 ^ n)) = Y), (3 : ℝ) ^ n / M =
      ∑ M ∈ MM, (3 : ℝ) ^ m / M *
        ∑ Y' ∈ Finset.univ.filter (fun Y' : ZMod (3 ^ n) => Y'.val % 3 ^ m = M % 3 ^ m), c Y' := by
  refine (fiber_aux MM _ (fun M => (3 : ℝ) ^ n / M)).trans (Finset.sum_congr rfl (fun M _ => ?_))
  have hv : (M : ZMod (3 ^ n)).val % 3 ^ m = M % 3 ^ m := by
    rw [ZMod.val_natCast, Nat.mod_mod_of_dvd _ (pow_dvd_pow 3 hmn)]
  have h3 : (3 : ℝ) ^ n ≠ 0 := by positivity
  have key : (3 : ℝ) ^ m / 3 ^ n * (3 ^ n / M) = 3 ^ m / M := by
    rw [div_mul_div_comm, mul_comm ((3 : ℝ) ^ n) (M : ℝ), mul_div_mul_right _ _ h3]
  simp only [hv]
  calc (3 : ℝ) ^ m / 3 ^ n *
        (∑ Y' ∈ Finset.univ.filter (fun Y' : ZMod (3 ^ n) => Y'.val % 3 ^ m = M % 3 ^ m), c Y') *
          (3 ^ n / M)
      = ((3 : ℝ) ^ m / 3 ^ n * (3 ^ n / M)) *
        ∑ Y' ∈ Finset.univ.filter (fun Y' : ZMod (3 ^ n) => Y'.val % 3 ^ m = M % 3 ^ m), c Y' := by ring
    _ = _ := by rw [key]

/-! ### S19 batch 3: Prop 1.14 enters (6e (v) assembled for the box sum). -/

def red (m n : ℕ) (Y : ZMod (3 ^ n)) : ZMod (3 ^ m) := (Y.val : ZMod (3 ^ m))

noncomputable def proj (m n : ℕ) (c : ZMod (3 ^ n) → ℝ) (Z : ZMod (3 ^ m)) : ℝ :=
  ∑ Y ∈ Finset.univ.filter (fun Y => red m n Y = Z), c Y

lemma avg_eq_proj [hCb : Fact CbS] (m n : ℕ) (c : ZMod (3 ^ n) → ℝ) (M : ℕ) :
    ∑ Y' ∈ Finset.univ.filter (fun Y' : ZMod (3 ^ n) => Y'.val % 3 ^ m = M % 3 ^ m), c Y' =
      proj m n c (M : ZMod (3 ^ m)) := by
  unfold proj red
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  ext Y
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact (ZMod.natCast_eq_natCast_iff' _ _ _).symm

/-- 6e (v) assembled: with `n = m + j`, the residue-weighted harmonic sum against `mu n K`
equals `β ·` the same sum at level `m` (independent of `j`), up to `H · Osc m n (mu n K)`.
`hproj` is `proj_mu` of `_syr.lean` (with `β = Σ_{Box j K} 2^{-|v|}`); `hH` is Lemma 5.3 (`c_bound`). -/
lemma main_v [hCb : Fact CbS] (m j K : ℕ) (MM : Finset ℕ) (β H : ℝ)
    (hproj : ∀ Z, proj m (m + j) (mu (m + j) K) Z = mu m K Z * β)
    (hH : ∀ Y : ZMod (3 ^ (m + j)),
      ∑ M ∈ MM.filter (fun M : ℕ => (M : ZMod (3 ^ (m + j))) = Y), (3 : ℝ) ^ (m + j) / M ≤ H) :
    |∑ M ∈ MM, (3 : ℝ) ^ (m + j) / M * mu (m + j) K (M : ZMod (3 ^ (m + j))) -
        β * ∑ M ∈ MM, (3 : ℝ) ^ m / M * mu m K (M : ZMod (3 ^ m))| ≤
      H * Osc m (m + j) (mu (m + j) K) := by
  have e1 : ∑ M ∈ MM, (3 : ℝ) ^ (m + j) / M * mu (m + j) K (M : ZMod (3 ^ (m + j))) =
      ∑ Y, mu (m + j) K Y *
        ∑ M ∈ MM.filter (fun M : ℕ => (M : ZMod (3 ^ (m + j))) = Y), (3 : ℝ) ^ (m + j) / M := by
    rw [fiber_aux]
    exact Finset.sum_congr rfl (fun M _ => mul_comm _ _)
  have e2 : β * ∑ M ∈ MM, (3 : ℝ) ^ m / M * mu m K (M : ZMod (3 ^ m)) =
      ∑ Y, ((3 : ℝ) ^ m / 3 ^ (m + j) *
        ∑ Y' ∈ Finset.univ.filter (fun Y' : ZMod (3 ^ (m + j)) => Y'.val % 3 ^ m = Y.val % 3 ^ m),
          mu (m + j) K Y') *
        ∑ M ∈ MM.filter (fun M : ℕ => (M : ZMod (3 ^ (m + j))) = Y), (3 : ℝ) ^ (m + j) / M := by
    rw [fiber_sum m (m + j) (by omega), Finset.mul_sum]
    refine Finset.sum_congr rfl (fun M _ => ?_)
    rw [avg_eq_proj, hproj]
    ring
  have h0 : ∀ Y : ZMod (3 ^ (m + j)), 0 ≤
      ∑ M ∈ MM.filter (fun M : ℕ => (M : ZMod (3 ^ (m + j))) = Y), (3 : ℝ) ^ (m + j) / M :=
    fun Y => Finset.sum_nonneg (fun M _ => by positivity)
  rw [e1, e2]
  exact osc_transfer m (m + j) _ _ H h0 hH

/-- 6e (v): dropping the deviation filter on `v` costs at most `H ·` the bad-prefix mass. -/
lemma box_minus (k K : ℕ) (AA : Finset (Fin k → ℕ)) (hAA : AA ⊆ Box k K)
    (h : (Fin k → ℕ) → ℝ) (H : ℝ) (h0 : ∀ v, 0 ≤ h v) (hH : ∀ v, h v ≤ H) :
    0 ≤ ∑ v ∈ Box k K, ((1 : ℝ) / 2) ^ absv v * h v - ∑ v ∈ AA, ((1 : ℝ) / 2) ^ absv v * h v ∧
    ∑ v ∈ Box k K, ((1 : ℝ) / 2) ^ absv v * h v - ∑ v ∈ AA, ((1 : ℝ) / 2) ^ absv v * h v ≤
      H * ∑ v ∈ Box k K \ AA, ((1 : ℝ) / 2) ^ absv v := by
  rw [← Finset.sum_sdiff hAA, add_sub_cancel_right, Finset.mul_sum]
  refine ⟨Finset.sum_nonneg (fun v _ => mul_nonneg (by positivity) (h0 v)),
    Finset.sum_le_sum (fun v _ => ?_)⟩
  rw [mul_comm H]
  exact mul_le_mul_of_nonneg_left (hH v) (by positivity)

/-! S20: 6e (vi) per-`n` bookkeeping, generic in the target window `S` (later `oddIcc y`). -/

/-- Numerator of `P_y(G_n)` (`prob_Gev`) with window `S`. -/
noncomputable def Gsum (k : ℕ) (AA : Finset (Fin k → ℕ)) (MM S : Finset ℕ) : ℝ :=
  ∑ p ∈ AA ×ˢ MM, (if 3 ^ k * Nof k p.1 p.2 + Sv (padv p.1) k = 2 ^ absv p.1 * p.2 ∧
    Nof k p.1 p.2 ∈ S then (1 : ℝ) / (Nof k p.1 p.2) else 0)

/-- Its model value: Lemma 2.1 congruence weighted by `3^k 2^{-|v|} / M`. -/
noncomputable def Rsum (k : ℕ) (AA : Finset (Fin k → ℕ)) (MM : Finset ℕ) : ℝ :=
  ∑ p ∈ AA ×ˢ MM, (if 3 ^ k * Nof k p.1 p.2 + Sv (padv p.1) k = 2 ^ absv p.1 * p.2 then
    (3 : ℝ) ^ k / (2 ^ absv p.1 * p.2) else 0)

lemma Rsum_nonneg (k : ℕ) (AA : Finset (Fin k → ℕ)) (MM : Finset ℕ) : 0 ≤ Rsum k AA MM :=
  Finset.sum_nonneg (fun p _ => by split_ifs <;> positivity)

/-- Upper bound, valid for every `n`. -/
lemma Gsum_le (k : ℕ) (AA : Finset (Fin k → ℕ)) (hAA : ∀ v ∈ AA, ∀ i, 1 ≤ v i)
    (MM S : Finset ℕ) (ε : ℝ) (hε : ε ≤ 1) (hMM : ∀ M ∈ MM, 2 * (3 / 2 : ℝ) ^ k ≤ ε * M) :
    Gsum k AA MM S ≤ (1 + ε) * Rsum k AA MM := by
  unfold Gsum Rsum
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun p hp => ?_)
  obtain ⟨hv, hM⟩ := Finset.mem_product.1 hp
  have hq : (0 : ℝ) ≤ 3 ^ k / (2 ^ absv p.1 * p.2) := by positivity
  have hε0 : 0 ≤ ε := by
    have h1 := hMM p.2 hM
    have h2 : (0 : ℝ) < 2 * (3 / 2 : ℝ) ^ k := by positivity
    by_contra hneg
    push_neg at hneg
    have : ε * (p.2 : ℝ) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hneg.le (by positivity)
    linarith
  by_cases hc : 3 ^ k * Nof k p.1 p.2 + Sv (padv p.1) k = 2 ^ absv p.1 * p.2
  · rw [if_pos hc]
    by_cases hS : Nof k p.1 p.2 ∈ S
    · rw [if_pos ⟨hc, hS⟩]
      rcases Nat.eq_zero_or_pos (Nof k p.1 p.2) with h0 | hpos
      · rw [h0]; simp; positivity
      · have hM2 : 2 * (3 / 2 : ℝ) ^ k ≤ p.2 := le_trans (hMM p.2 hM) (by
          have : (0 : ℝ) ≤ p.2 := by positivity
          nlinarith)
        obtain ⟨-, -, -, h4⟩ := nof_approx k p.1 (hAA p.1 hv) p.2 _ hpos hc hM2
        have hMpos : (0 : ℝ) < p.2 := lt_of_lt_of_le (by positivity) hM2
        have hc' : 2 * ((3 / 2 : ℝ) ^ k / p.2) ≤ ε := by
          rw [← mul_div_assoc, div_le_iff₀ hMpos]; exact hMM p.2 hM
        (first | linarith [mul_le_mul_of_nonneg_right hc' hq] | nlinarith [mul_le_mul_of_nonneg_right hc' hq])
    · rw [if_neg (fun h => hS h.2)]; positivity
  · rw [if_neg (fun h => hc h.1), if_neg hc]; simp

/-- Lower bound for interior `n`: every congruent pair lands in the window. -/
lemma Rsum_le_Gsum (k : ℕ) (AA : Finset (Fin k → ℕ)) (hAA : ∀ v ∈ AA, ∀ i, 1 ≤ v i)
    (MM S : Finset ℕ) (h0S : 0 ∉ S) (hMM : ∀ M ∈ MM, 2 * (3 / 2 : ℝ) ^ k ≤ M)
    (hin : ∀ p ∈ AA ×ˢ MM, 3 ^ k * Nof k p.1 p.2 + Sv (padv p.1) k = 2 ^ absv p.1 * p.2 →
      Nof k p.1 p.2 ∈ S) :
    Rsum k AA MM ≤ Gsum k AA MM S := by
  unfold Gsum Rsum
  refine Finset.sum_le_sum (fun p hp => ?_)
  obtain ⟨hv, hM⟩ := Finset.mem_product.1 hp
  by_cases hc : 3 ^ k * Nof k p.1 p.2 + Sv (padv p.1) k = 2 ^ absv p.1 * p.2
  · have hS := hin p hp hc
    rw [if_pos hc, if_pos ⟨hc, hS⟩]
    have hpos : 0 < Nof k p.1 p.2 := Nat.pos_of_ne_zero (fun h => h0S (h ▸ hS))
    obtain ⟨-, -, h3, -⟩ := nof_approx k p.1 (hAA p.1 hv) p.2 _ hpos hc (hMM p.2 hM)
    linarith
  · rw [if_neg hc, if_neg (fun h => hc h.1)]

/-- Exterior `n`: no congruent pair lands in the window. -/
lemma Gsum_eq_zero (k : ℕ) (AA : Finset (Fin k → ℕ)) (MM S : Finset ℕ)
    (hout : ∀ p ∈ AA ×ˢ MM, 3 ^ k * Nof k p.1 p.2 + Sv (padv p.1) k = 2 ^ absv p.1 * p.2 →
      Nof k p.1 p.2 ∉ S) :
    Gsum k AA MM S = 0 := by
  unfold Gsum
  refine Finset.sum_eq_zero (fun p hp => ?_)
  rw [if_neg (fun h => hout p hp h.1 h.2)]

/-- `log N` from the two-sided size bound of `nof_approx`. -/
lemma nof_log (k a M N : ℕ) (hN : 0 < N) (h1 : (3 : ℝ) ^ k * N ≤ 2 ^ a * M)
    (h2 : (2 : ℝ) ^ a * M ≤ 2 * 3 ^ k * N) :
    |Real.log N - (a * Real.log 2 + Real.log M - k * Real.log 3)| ≤ Real.log 2 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hM0 : (0 : ℝ) < M := by
    have : (0 : ℝ) < 3 ^ k * N := by positivity
    have h2a : (0 : ℝ) < 2 ^ a := by positivity
    by_contra h; push_neg at h
    (first | linarith [mul_nonpos_of_nonneg_of_nonpos h2a.le h] | nlinarith [mul_nonpos_of_nonneg_of_nonpos h2a.le h])
  have l1 := Real.log_le_log (by positivity) h1
  have l2 := Real.log_le_log (by positivity) h2
  rw [Real.log_mul (by positivity) hN0.ne', Real.log_mul (by positivity) hM0.ne',
    Real.log_pow, Real.log_pow] at l1
  rw [Real.log_mul (by positivity) hM0.ne', Real.log_mul (by positivity) hN0.ne',
    Real.log_mul (by norm_num) (by positivity), Real.log_pow, Real.log_pow] at l2
  rw [abs_le]; constructor <;> linarith

lemma log43 : Real.log (4 / 3) = 2 * Real.log 2 - Real.log 3 := by
  rw [Real.log_div (by norm_num) (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
  push_cast; ring

/-- Window of `log N_{v,M}` for a deviation-good `v` and `M ∈ E'`. -/
lemma nof_window (k m0 a M N : ℕ) (L0 D W : ℝ) (hN : 0 < N) (h1 : (3 : ℝ) ^ k * N ≤ 2 ^ a * M)
    (h2 : (2 : ℝ) ^ a * M ≤ 2 * 3 ^ k * N) (ha : |(a : ℝ) - 2 * k| ≤ D)
    (hM : |Real.log M - (L0 + m0 * Real.log (4 / 3))| ≤ W) :
    |Real.log N - (L0 + ((m0 + k : ℕ) : ℝ) * Real.log (4 / 3))| ≤
      W + D * Real.log 2 + Real.log 2 := by
  have h := nof_log k a M N hN h1 h2
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hd : |((a : ℝ) - 2 * k) * Real.log 2| ≤ D * Real.log 2 := by
    rw [abs_mul, abs_of_pos hl2]; exact mul_le_mul_of_nonneg_right ha hl2.le
  have e : Real.log N - (L0 + ((m0 + k : ℕ) : ℝ) * Real.log (4 / 3)) =
      (Real.log N - (a * Real.log 2 + Real.log M - k * Real.log 3)) +
      ((a : ℝ) - 2 * k) * Real.log 2 + (Real.log M - (L0 + m0 * Real.log (4 / 3))) := by
    rw [log43]; push_cast; ring
  rw [e]
  calc _ ≤ |(Real.log N - (a * Real.log 2 + Real.log M - k * Real.log 3)) +
        ((a : ℝ) - 2 * k) * Real.log 2| + |Real.log M - (L0 + m0 * Real.log (4 / 3))| :=
        abs_add_le _ _
    _ ≤ (|Real.log N - (a * Real.log 2 + Real.log M - k * Real.log 3)| +
        |((a : ℝ) - 2 * k) * Real.log 2|) + |Real.log M - (L0 + m0 * Real.log (4 / 3))| := by
        gcongr; exact abs_add_le _ _
    _ ≤ _ := by linarith

/-- 6e (v) assembled: the model sum at level `k = m + j` is `β ·` the level-`m` harmonic sum
up to the Prop 1.14 oscillation and the deviation-bad mass. -/
lemma Rsum_approx [hCb : Fact CbS] (m j K : ℕ) (AA : Finset (Fin (m + j) → ℕ)) (hAAB : AA ⊆ Box (m + j) K)
    (MM : Finset ℕ) (hMM : ∀ M ∈ MM, (3 / 2 : ℝ) ^ (m + j) ≤ M) (β H : ℝ)
    (hproj : ∀ Z, proj m (m + j) (mu (m + j) K) Z = mu m K Z * β)
    (hH : ∀ Y : ZMod (3 ^ (m + j)),
      ∑ M ∈ MM.filter (fun M : ℕ => (M : ZMod (3 ^ (m + j))) = Y), (3 : ℝ) ^ (m + j) / M ≤ H) :
    |Rsum (m + j) AA MM - β * ∑ M ∈ MM, (3 : ℝ) ^ m / M * mu m K (M : ZMod (3 ^ m))| ≤
      H * Osc m (m + j) (mu (m + j) K) + H * ∑ v ∈ Box (m + j) K \ AA, ((1 : ℝ) / 2) ^ absv v := by
  have hAA : ∀ v ∈ AA, ∀ i, 1 ≤ v i := fun v hv i =>
    (Finset.mem_Icc.1 (Fintype.mem_piFinset.1 (hAAB hv) i)).1
  have e1 : Rsum (m + j) AA MM = ∑ v ∈ AA, ((1 : ℝ) / 2) ^ absv v *
      ∑ M ∈ MM.filter (fun M : ℕ => (M : ZMod (3 ^ (m + j))) = syrZ (m + j) (padv (revv v))),
        (3 : ℝ) ^ (m + j) / M := sumq_eq (m + j) AA hAA MM hMM
  obtain ⟨b1, b2⟩ := box_minus (m + j) K AA hAAB
    (fun v => ∑ M ∈ MM.filter (fun M : ℕ => (M : ZMod (3 ^ (m + j))) = syrZ (m + j) (padv (revv v))),
        (3 : ℝ) ^ (m + j) / M) H
    (fun v => Finset.sum_nonneg (fun M _ => by positivity)) (fun v => hH _)
  rw [sumBox_eq_mu] at b1 b2
  have hmv := main_v m j K MM β H hproj hH
  rw [e1]
  rw [abs_le] at hmv ⊢
  constructor <;> linarith [hmv.1, hmv.2]

/-- Bound on the model sum used for boundary `n`: `Rsum ≤ H` (total Box weight is `≤ 1`). -/
lemma Rsum_le_H (k K : ℕ) (AA : Finset (Fin k → ℕ)) (hAAB : AA ⊆ Box k K)
    (MM : Finset ℕ) (hMM : ∀ M ∈ MM, (3 / 2 : ℝ) ^ k ≤ M) (H : ℝ) (hH0 : 0 ≤ H)
    (hH : ∀ Y : ZMod (3 ^ k),
      ∑ M ∈ MM.filter (fun M : ℕ => (M : ZMod (3 ^ k)) = Y), (3 : ℝ) ^ k / M ≤ H) :
    Rsum k AA MM ≤ H * ∑ v ∈ AA, ((1 : ℝ) / 2) ^ absv v := by
  have hAA : ∀ v ∈ AA, ∀ i, 1 ≤ v i := fun v hv i =>
    (Finset.mem_Icc.1 (Fintype.mem_piFinset.1 (hAAB hv) i)).1
  unfold Rsum
  rw [sumq_eq k AA hAA MM hMM, Finset.mul_sum]
  refine Finset.sum_le_sum (fun v _ => ?_)
  rw [mul_comm H]
  exact mul_le_mul_of_nonneg_left (hH _) (by positivity)

/-- 6f abstract window sum: interior `n` contribute `Λ` each, boundary `n` at most
`(1+ε) H0`, exterior `n` nothing. -/
lemma sum_window (I Int Bd : Finset ℕ) (hInt : Int ⊆ I) (hBd : Bd ⊆ I) (hdis : Disjoint Int Bd)
    (G R e : ℕ → ℝ) (Λ ε H0 : ℝ) (hε : 0 ≤ ε)
    (hG0 : ∀ n ∈ I, 0 ≤ G n) (hGR : ∀ n ∈ I, G n ≤ (1 + ε) * R n) (hRH : ∀ n ∈ I, R n ≤ H0)
    (hRG : ∀ n ∈ Int, R n ≤ G n) (hext : ∀ n ∈ I, n ∉ Int → n ∉ Bd → G n = 0)
    (hRL : ∀ n ∈ Int, |R n - Λ| ≤ e n) :
    |∑ n ∈ I, G n - Int.card * Λ| ≤
      ε * Int.card * H0 + ∑ n ∈ Int, e n + (1 + ε) * Bd.card * H0 := by
  have hsplit : ∑ n ∈ I, G n = ∑ n ∈ Int, G n + ∑ n ∈ Bd, G n := by
    rw [← Finset.sum_union hdis]
    refine (Finset.sum_subset (Finset.union_subset hInt hBd) (fun n hn hn' => ?_)).symm
    rw [Finset.mem_union, not_or] at hn'
    exact hext n hn hn'.1 hn'.2
  have hB0 : 0 ≤ ∑ n ∈ Bd, G n := Finset.sum_nonneg (fun n hn => hG0 n (hBd hn))
  have hB1 : ∑ n ∈ Bd, G n ≤ (1 + ε) * Bd.card * H0 := by
    calc ∑ n ∈ Bd, G n ≤ ∑ n ∈ Bd, (1 + ε) * H0 := Finset.sum_le_sum (fun n hn =>
          le_trans (hGR n (hBd hn)) (mul_le_mul_of_nonneg_left (hRH n (hBd hn)) (by linarith)))
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]; ring
  have hI1 : |∑ n ∈ Int, G n - Int.card * Λ| ≤ ε * Int.card * H0 + ∑ n ∈ Int, e n := by
    have e0 : ∑ n ∈ Int, G n - Int.card * Λ =
        ∑ n ∈ Int, (G n - R n) + ∑ n ∈ Int, (R n - Λ) := by
      rw [← Finset.sum_add_distrib]
      simp only [sub_add_sub_cancel]
      rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    rw [e0]
    have a1 : |∑ n ∈ Int, (G n - R n)| ≤ ε * Int.card * H0 := by
      calc |∑ n ∈ Int, (G n - R n)| ≤ ∑ n ∈ Int, |G n - R n| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ n ∈ Int, ε * H0 := Finset.sum_le_sum (fun n hn => by
            have h1 := hRG n hn
            have h2 := hGR n (hInt hn)
            have h3 := hRH n (hInt hn)
            have h5 := hG0 n (hInt hn)
            have h4 : 0 ≤ R n := by
              by_contra hneg
              push Not at hneg
              have : (1 + ε) * R n < 0 := mul_neg_of_pos_of_neg (by linarith) hneg
              linarith
            rw [abs_of_nonneg (by linarith)]
            have h6 : ε * R n ≤ ε * H0 := mul_le_mul_of_nonneg_left h3 hε
            nlinarith)
        _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]; ring
    have a2 : |∑ n ∈ Int, (R n - Λ)| ≤ ∑ n ∈ Int, e n :=
      le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum hRL)
    exact le_trans (abs_add_le _ _) (by linarith)
  rw [hsplit]
  rw [abs_le] at hI1 ⊢
  constructor <;> linarith [hI1.1, hI1.2]

/-- 6f lattice count: the number of `n` with `a ≤ n h ≤ b` is `(b - a)/h ± 1`. -/
lemma card_window (I : Finset ℕ) (a b h : ℝ) (hh : 0 < h) (ha : 0 ≤ a) (hab : a ≤ b)
    (hI : ∀ n : ℕ, a ≤ n * h → n * h ≤ b → n ∈ I) :
    (b - a) / h - 1 ≤ ((I.filter (fun n : ℕ => a ≤ n * h ∧ n * h ≤ b)).card : ℝ) ∧
    ((I.filter (fun n : ℕ => a ≤ n * h ∧ n * h ≤ b)).card : ℝ) ≤ (b - a) / h + 1 := by
  have hb : 0 ≤ b / h := div_nonneg (le_trans ha hab) hh.le
  have ha' : 0 ≤ a / h := div_nonneg ha hh.le
  have heq : I.filter (fun n : ℕ => a ≤ n * h ∧ n * h ≤ b) = Finset.Icc ⌈a / h⌉₊ ⌊b / h⌋₊ := by
    ext n
    rw [Finset.mem_filter, Finset.mem_Icc, Nat.ceil_le, Nat.le_floor_iff hb,
      div_le_iff₀ hh, le_div_iff₀ hh]
    constructor
    · intro h; exact h.2
    · intro h; exact ⟨hI n h.1 h.2, h⟩
  rw [heq, Nat.card_Icc]
  have f1 := Nat.floor_le hb
  have f2 := Nat.lt_floor_add_one (b / h)
  have c1 := Nat.le_ceil (a / h)
  have c2 := Nat.ceil_lt_add_one ha'
  have hd : (b - a) / h = b / h - a / h := sub_div _ _ _
  rw [hd]
  by_cases hc : ⌈a / h⌉₊ ≤ ⌊b / h⌋₊ + 1
  · rw [Nat.cast_sub hc]
    push_cast
    constructor <;> linarith
  · push Not at hc
    rw [Nat.sub_eq_zero_of_le hc.le]
    have hc' : (⌊b / h⌋₊ : ℝ) + 1 < ⌈a / h⌉₊ := by exact_mod_cast hc
    push_cast
    constructor <;> linarith [div_le_div_of_nonneg_right hab hh.le]

/-- 6f normalisation: `#interior · Λ / Z_y ≈ 2Λ / log(4/3)` (with `L = (α-1) log y`, `Z_y ≈ L/2`
by `Z_asymp`, `#interior ≈ L / h` by `card_window`). -/
lemma ratio_close (c Z L Λ h u : ℝ) (hL : 4 ≤ L) (hZ : |Z - L / 2| ≤ 1) (hc : |c - L / h| ≤ u)
    (hΛ : 0 ≤ Λ) (hh : 0 < h) :
    |c * Λ / Z - 2 * Λ / h| ≤ Λ * (4 * (u + 2 / h) / L) := by
  rw [abs_le] at hZ
  have hZ0 : L / 4 ≤ Z := by linarith
  have hZp : 0 < Z := by linarith
  have e : c * Λ / Z - 2 * Λ / h = Λ * (((c - L / h) + (L - 2 * Z) / h) / Z) := by
    field_simp; ring
  rw [e, abs_mul, abs_of_nonneg hΛ]
  refine mul_le_mul_of_nonneg_left ?_ hΛ
  rw [abs_div, abs_of_pos hZp, div_le_div_iff₀ hZp (by linarith)]
  have h1 : |(c - L / h) + (L - 2 * Z) / h| ≤ u + 2 / h := by
    refine le_trans (abs_add_le _ _) (add_le_add hc ?_)
    rw [abs_div, abs_of_pos hh]
    exact div_le_div_of_nonneg_right (by rw [abs_le]; constructor <;> linarith) hh.le
  have h2 : 0 ≤ u + 2 / h := le_trans (abs_nonneg _) h1
  nlinarith [mul_le_mul_of_nonneg_right h1 (by linarith : (0 : ℝ) ≤ L),
    mul_le_mul_of_nonneg_left hZ0 (by linarith : (0 : ℝ) ≤ 4 * (u + 2 / h))]


/-! S21 (item 6f, step 1): the per-`y` window estimate, abstract in the target set `S = oddIcc y`. -/

lemma geo_one' (K : ℕ) : ∑ j ∈ Finset.Icc 1 K, ((1 : ℝ) / 2) ^ j = 1 - (1 / 2) ^ K := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, pow_succ]; ring

lemma box_mass_le (k K : ℕ) (AA : Finset (Fin k → ℕ)) (hAA : AA ⊆ Box k K) :
    ∑ v ∈ AA, ((1 : ℝ) / 2) ^ absv v ≤ 1 := by
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hAA (fun _ _ _ => by positivity)) ?_
  have e : ∑ v ∈ Box k K, ((1 : ℝ) / 2) ^ absv v =
      ∏ _i : Fin k, ∑ a ∈ Finset.Icc 1 K, ((1 : ℝ) / 2) ^ a := by
    rw [Finset.prod_univ_sum]
    unfold Box absv
    refine Finset.sum_congr rfl (fun v _ => ?_)
    rw [Finset.prod_pow_eq_pow_sum]
  rw [e]
  refine Finset.prod_le_one (fun _ _ => by positivity) (fun _ _ => ?_)
  rw [geo_one']
  have : (0 : ℝ) ≤ (1 / 2) ^ K := by positivity
  linarith

lemma Gsum_nonneg (k : ℕ) (AA : Finset (Fin k → ℕ)) (MM S : Finset ℕ) : 0 ≤ Gsum k AA MM S :=
  Finset.sum_nonneg (fun p _ => by split_ifs <;> positivity)

/-- Per-`y` window estimate: `∑_{n ∈ [m0,n0]} G_n = #Int · Λ + O(...)`, `Λ = ∑_M 3^m0/M μ_m0(M)`. -/
lemma win_y [hCb : Fact CbS] (m0 n0 K : ℕ) (AA : (k : ℕ) → Finset (Fin k → ℕ)) (hAAB : ∀ k, AA k ⊆ Box k K)
    (MM S : Finset ℕ) (h0S : 0 ∉ S) (ε H : ℝ) (hε0 : 0 ≤ ε) (hε : ε ≤ 1) (hH0 : 0 ≤ H)
    (hMM : ∀ M ∈ MM, 2 * (3 / 2 : ℝ) ^ n0 ≤ ε * M)
    (hH : ∀ k ≤ n0, ∀ Y : ZMod (3 ^ k),
      ∑ M ∈ MM.filter (fun M : ℕ => (M : ZMod (3 ^ k)) = Y), (3 : ℝ) ^ k / M ≤ H)
    (β : ℕ → ℝ) (hproj : ∀ j Z, proj m0 (m0 + j) (mu (m0 + j) K) Z = mu m0 K Z * β j)
    (Int Bd : Finset ℕ) (hInt : Int ⊆ Finset.Icc m0 n0) (hBd : Bd ⊆ Finset.Icc m0 n0)
    (hdis : Disjoint Int Bd) (hInt2 : ∀ n ∈ Int, 2 * m0 ≤ n)
    (hin : ∀ n ∈ Int, ∀ p ∈ AA (n - m0) ×ˢ MM,
      3 ^ (n - m0) * Nof (n - m0) p.1 p.2 + Sv (padv p.1) (n - m0) = 2 ^ absv p.1 * p.2 →
        Nof (n - m0) p.1 p.2 ∈ S)
    (hout : ∀ n ∈ Finset.Icc m0 n0, n ∉ Int → n ∉ Bd → ∀ p ∈ AA (n - m0) ×ˢ MM,
      3 ^ (n - m0) * Nof (n - m0) p.1 p.2 + Sv (padv p.1) (n - m0) = 2 ^ absv p.1 * p.2 →
        Nof (n - m0) p.1 p.2 ∉ S) :
    |∑ n ∈ Finset.Icc m0 n0, Gsum (n - m0) (AA (n - m0)) MM S -
        Int.card * ∑ M ∈ MM, (3 : ℝ) ^ m0 / M * mu m0 K (M : ZMod (3 ^ m0))| ≤
      ε * Int.card * H + ∑ n ∈ Int, (|β (n - 2 * m0) - 1| *
          |∑ M ∈ MM, (3 : ℝ) ^ m0 / M * mu m0 K (M : ZMod (3 ^ m0))| +
        H * Osc m0 (n - m0) (mu (n - m0) K) +
        H * ∑ v ∈ Box (n - m0) K \ AA (n - m0), ((1 : ℝ) / 2) ^ absv v) +
      (1 + ε) * Bd.card * H := by
  set Λ := ∑ M ∈ MM, (3 : ℝ) ^ m0 / M * mu m0 K (M : ZMod (3 ^ m0)) with hΛ
  have hMkε : ∀ k ≤ n0, ∀ M ∈ MM, 2 * (3 / 2 : ℝ) ^ k ≤ ε * M := fun k hk M hM => by
    have h1 : (3 / 2 : ℝ) ^ k ≤ (3 / 2) ^ n0 := pow_le_pow_right₀ (by norm_num) hk
    linarith [hMM M hM]
  have hMk : ∀ k ≤ n0, ∀ M ∈ MM, 2 * (3 / 2 : ℝ) ^ k ≤ M := fun k hk M hM => by
    have h2 := hMkε k hk M hM
    have h0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    have h3 : ε * (M : ℝ) ≤ M := by (first | linarith | nlinarith)
    linarith
  have hMk1 : ∀ k ≤ n0, ∀ M ∈ MM, (3 / 2 : ℝ) ^ k ≤ M := fun k hk M hM => by
    have h2 := hMk k hk M hM
    have : (0 : ℝ) ≤ (3 / 2) ^ k := by positivity
    linarith
  have hpos : ∀ k, ∀ v ∈ AA k, ∀ i, 1 ≤ v i := fun k v hv i =>
    (Finset.mem_Icc.1 (Fintype.mem_piFinset.1 (hAAB k hv) i)).1
  have hle : ∀ n ∈ Finset.Icc m0 n0, n - m0 ≤ n0 := fun n hn => by
    have := (Finset.mem_Icc.1 hn).2; omega
  have key : ∀ k j, k = m0 + j → k ≤ n0 →
      |Rsum k (AA k) MM - Λ| ≤ |β j - 1| * |Λ| + H * Osc m0 k (mu k K) +
        H * ∑ v ∈ Box k K \ AA k, ((1 : ℝ) / 2) ^ absv v := by
    rintro k j rfl hk
    have h := Rsum_approx m0 j K (AA (m0 + j)) (hAAB _) MM (hMk1 _ hk) (β j) H (hproj j)
      (hH _ hk)
    have e : Rsum (m0 + j) (AA (m0 + j)) MM - Λ =
        (Rsum (m0 + j) (AA (m0 + j)) MM - β j * Λ) + (β j - 1) * Λ := by ring
    rw [e]
    refine le_trans (abs_add_le _ _) ?_
    rw [abs_mul]
    linarith
  exact sum_window (Finset.Icc m0 n0) Int Bd hInt hBd hdis
    (fun n => Gsum (n - m0) (AA (n - m0)) MM S) (fun n => Rsum (n - m0) (AA (n - m0)) MM)
    (fun n => |β (n - 2 * m0) - 1| * |Λ| + H * Osc m0 (n - m0) (mu (n - m0) K) +
        H * ∑ v ∈ Box (n - m0) K \ AA (n - m0), ((1 : ℝ) / 2) ^ absv v)
    Λ ε H hε0
    (fun n _ => Gsum_nonneg _ _ _ _)
    (fun n hn => Gsum_le _ _ (hpos _) MM S ε hε (hMkε _ (hle n hn)))
    (fun n hn => le_trans (Rsum_le_H _ K _ (hAAB _) MM (hMk1 _ (hle n hn)) H hH0 (hH _ (hle n hn)))
      (mul_le_of_le_one_right hH0 (box_mass_le _ K _ (hAAB _))))
    (fun n hn => Rsum_le_Gsum _ _ (hpos _) MM S h0S (hMk _ (hle n (hInt hn))) (hin n hn))
    (fun n hn h1 h2 => Gsum_eq_zero _ _ MM S (hout n hn h1 h2))
    (fun n hn => key (n - m0) (n - 2 * m0) (by have := hInt2 n hn; omega) (hle n (hInt hn)))

/-- Ratio step of 6f: `P_y = G/Z` is close to the `y`-independent value `2Λ/h`. -/
lemma P_close (G c Z L Λ h u Err : ℝ) (hL : 4 ≤ L) (hZ : |Z - L / 2| ≤ 1) (hc : |c - L / h| ≤ u)
    (hΛ : 0 ≤ Λ) (hh : 0 < h) (hG : |G - c * Λ| ≤ Err) :
    |G / Z - 2 * Λ / h| ≤ 4 * Err / L + Λ * (4 * (u + 2 / h) / L) := by
  have hZ0 : L / 4 ≤ Z := by rw [abs_le] at hZ; linarith
  have hZp : 0 < Z := by linarith
  have hr := ratio_close c Z L Λ h u hL hZ hc hΛ hh
  have e : G / Z - 2 * Λ / h = (G - c * Λ) / Z + (c * Λ / Z - 2 * Λ / h) := by ring
  rw [e]
  refine le_trans (abs_add_le _ _) (add_le_add ?_ hr)
  rw [abs_div, abs_of_pos hZp, div_le_div_iff₀ hZp (by linarith)]
  have hE : 0 ≤ Err := le_trans (abs_nonneg _) hG
  (first | linarith [mul_le_mul_of_nonneg_left hZ0 hE, mul_le_mul_of_nonneg_right hG (by linarith : (0 : ℝ) ≤ L)] | nlinarith [mul_le_mul_of_nonneg_left hZ0 hE, mul_le_mul_of_nonneg_right hG (by linarith : (0 : ℝ) ≤ L)])

lemma mu_nonneg (n K : ℕ) (Y : ZMod (3 ^ n)) : 0 ≤ mu n K Y :=
  Finset.sum_nonneg (fun _ _ => by positivity)

lemma mu_total (n K : ℕ) : ∑ Y : ZMod (3 ^ n), mu n K Y ≤ 1 := by
  unfold mu
  rw [Finset.sum_fiberwise (Box n K) (fun w => syrZ n (padv w))
    (fun w => ((1 : ℝ) / 2) ^ (∑ i, w i))]
  exact box_mass_le n K _ subset_rfl

/-- `Λ ≤ H`: the limit value is bounded by the residue-class harmonic bound (Lemma 5.3 at level `m`). -/
lemma Lam_le_H (m K : ℕ) (MM : Finset ℕ) (H : ℝ) (hH0 : 0 ≤ H)
    (hH : ∀ Y : ZMod (3 ^ m),
      ∑ M ∈ MM.filter (fun M : ℕ => (M : ZMod (3 ^ m)) = Y), (3 : ℝ) ^ m / M ≤ H) :
    ∑ M ∈ MM, (3 : ℝ) ^ m / M * mu m K (M : ZMod (3 ^ m)) ≤ H := by
  rw [← Finset.sum_fiberwise MM (fun M : ℕ => (M : ZMod (3 ^ m)))
    (fun M : ℕ => (3 : ℝ) ^ m / M * mu m K (M : ZMod (3 ^ m)))]
  calc ∑ Y : ZMod (3 ^ m), ∑ M ∈ MM.filter (fun M : ℕ => (M : ZMod (3 ^ m)) = Y),
        (3 : ℝ) ^ m / M * mu m K (M : ZMod (3 ^ m))
      = ∑ Y : ZMod (3 ^ m), mu m K Y * ∑ M ∈ MM.filter (fun M : ℕ => (M : ZMod (3 ^ m)) = Y),
        (3 : ℝ) ^ m / M := by
        refine Finset.sum_congr rfl (fun Y _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun M hM => ?_)
        rw [(Finset.mem_filter.1 hM).2]; ring
    _ ≤ ∑ Y : ZMod (3 ^ m), mu m K Y * H :=
        Finset.sum_le_sum (fun Y _ => mul_le_mul_of_nonneg_left (hH Y) (mu_nonneg _ _ _))
    _ = H * ∑ Y : ZMod (3 ^ m), mu m K Y := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun _ _ => by ring)
    _ ≤ H := mul_le_of_le_one_right hH0 (mu_total m K)

/-- The Section 5 main sum as a `Gsum` sum over `S = oddIcc y` (bridge from `prob_Gev`). -/
lemma sum_prob_Gev (y x W D : ℝ) (m0 n0 K Mmax : ℕ) (E : ℕ → Prop) :
    ∑ n ∈ Finset.Icc m0 n0, prob y (Gev x W D m0 K Mmax E n) =
      (∑ n ∈ Finset.Icc m0 n0,
        Gsum (n - m0) (AAk D K (n - m0)) (MMs x W D m0 Mmax E) (oddIcc y)) / Z y := by
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [prob_Gev]
  rfl

end Item6e5

section Item6f2
open Classical

/-- `|v| ≈ 2k` for deviation-good prefixes. -/
lemma absv_dev {D : ℝ} (hD : 0 ≤ D) {K k : ℕ} {v : Fin k → ℕ} (hv : v ∈ AAk D K k) :
    |(absv v : ℝ) - 2 * k| ≤ D := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk; simp [absv, hD]
  · have h := (Finset.mem_filter.1 hv).2 k (Finset.mem_Icc.2 ⟨hk, le_rfl⟩)
    rwa [ps_eq_Av, Av_padv] at h

/-- Log-size window of `N_{v,M}` for `v ∈ AAk`, `M ∈ MMs`. -/
lemma nof_win {x W D : ℝ} (hD : 0 ≤ D) {m0 K Mmax k : ℕ} {E : ℕ → Prop}
    {v : Fin k → ℕ} (hv : v ∈ AAk D K k) {M : ℕ} (hM : M ∈ MMs x W D m0 Mmax E)
    (hMk : 2 * (3 / 2 : ℝ) ^ k ≤ M) {N : ℕ} (hN : 0 < N)
    (h : 3 ^ k * N + Sv (padv v) k = 2 ^ absv v * M) :
    |Real.log N - (Real.log x + ((m0 + k : ℕ) : ℝ) * Real.log (4 / 3))| ≤
      W + D * Real.log 2 + Real.log 2 := by
  have hpos : ∀ i, 1 ≤ v i := fun i =>
    (Finset.mem_Icc.1 (Fintype.mem_piFinset.1 (Finset.mem_filter.1 hv).1 i)).1
  obtain ⟨h1, h2, -, -⟩ := nof_approx k v hpos M N hN h hMk
  obtain ⟨-, ⟨-, -, -, hW⟩, -⟩ := (Finset.mem_filter.1 hM).2
  exact nof_window k m0 (absv v) M N (Real.log x) D W hN h1 h2 (absv_dev hD hv) hW

lemma mem_oddIcc_of_log {y : ℝ} (hy : 0 < y) {N : ℕ} (hNo : Odd N)
    (h1 : Real.log y ≤ Real.log N) (h2 : Real.log N ≤ alph * Real.log y) : N ∈ oddIcc y := by
  have hN : (0 : ℝ) < N := by exact_mod_cast hNo.pos
  have hyN : y ≤ N := (Real.log_le_log_iff hy hN).1 h1
  have hya : 0 < y ^ alph := Real.rpow_pos_of_pos hy _
  have hNy : (N : ℝ) ≤ y ^ alph := by
    rw [← Real.log_le_log_iff hN hya, Real.log_rpow hy]; exact h2
  unfold oddIcc
  exact Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨Nat.ceil_le.2 hyN, Nat.le_floor hNy⟩, hNo⟩

lemma not_mem_oddIcc_of_log {y : ℝ} (hy : 0 < y) {N : ℕ} (hN : 0 < N)
    (h : Real.log N < Real.log y ∨ alph * Real.log y < Real.log N) : N ∉ oddIcc y := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  intro hmem
  obtain ⟨h1, -⟩ := Finset.mem_filter.1 hmem
  obtain ⟨hl, hu⟩ := Finset.mem_Icc.1 h1
  have hyN : y ≤ N := le_trans (Nat.le_ceil y) (by exact_mod_cast hl)
  have hya : 0 < y ^ alph := Real.rpow_pos_of_pos hy _
  have hNy : (N : ℝ) ≤ y ^ alph := le_trans (by exact_mod_cast hu) (Nat.floor_le hya.le)
  rcases h with h | h
  · exact absurd (Real.log_le_log hy hyN) (not_le.2 h)
  · have := Real.log_le_log hN' hNy
    rw [Real.log_rpow hy] at this; linarith

lemma two_pow_mono_M {n0 k : ℕ} (hk : k ≤ n0) {M : ℕ} (hM : 2 * (3 / 2 : ℝ) ^ n0 ≤ M) :
    2 * (3 / 2 : ℝ) ^ k ≤ M :=
  le_trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) hk) (by norm_num)) hM

/-- Interior window: `N_{v,M}` lands in `[y, y^α]`. -/
lemma win_in {x y W D Wt : ℝ} (hD : 0 ≤ D) (hy : 0 < y)
    (hWt : W + D * Real.log 2 + Real.log 2 ≤ Wt)
    {m0 n0 K Mmax n : ℕ} {E : ℕ → Prop} (hm0 : 1 ≤ m0)
    (hMk : ∀ M ∈ MMs x W D m0 Mmax E, 2 * (3 / 2 : ℝ) ^ n0 ≤ M)
    (hn : 2 * m0 ≤ n) (hn0 : n ≤ n0)
    (hlo : Real.log y - Real.log x + Wt ≤ n * Real.log (4 / 3))
    (hhi : n * Real.log (4 / 3) ≤ alph * Real.log y - Real.log x - Wt)
    {v : Fin (n - m0) → ℕ} (hv : v ∈ AAk D K (n - m0)) {M : ℕ} (hM : M ∈ MMs x W D m0 Mmax E)
    (h : 3 ^ (n - m0) * Nof (n - m0) v M + Sv (padv v) (n - m0) = 2 ^ absv v * M) :
    Nof (n - m0) v M ∈ oddIcc y := by
  have hpos : ∀ i, 1 ≤ v i := fun i =>
    (Finset.mem_Icc.1 (Fintype.mem_piFinset.1 (Finset.mem_filter.1 hv).1 i)).1
  have hodd := cong_odd (by omega) v hpos h
  have hw := nof_win hD hv hM (two_pow_mono_M (by omega) (hMk M hM)) hodd.pos h
  rw [show m0 + (n - m0) = n by omega, abs_le] at hw
  exact mem_oddIcc_of_log hy hodd (by linarith) (by linarith)

/-- Exterior window: `N_{v,M}` misses `[y, y^α]`. -/
lemma win_out {x y W D Wt : ℝ} (hD : 0 ≤ D) (hy : 0 < y)
    (hWt : W + D * Real.log 2 + Real.log 2 ≤ Wt)
    {m0 n0 K Mmax n : ℕ} {E : ℕ → Prop}
    (hMk : ∀ M ∈ MMs x W D m0 Mmax E, 2 * (3 / 2 : ℝ) ^ n0 ≤ M)
    (hn : m0 ≤ n) (hn0 : n ≤ n0)
    (hout : n * Real.log (4 / 3) < Real.log y - Real.log x - Wt ∨
      alph * Real.log y - Real.log x + Wt < n * Real.log (4 / 3))
    {v : Fin (n - m0) → ℕ} (hv : v ∈ AAk D K (n - m0)) {M : ℕ} (hM : M ∈ MMs x W D m0 Mmax E)
    (h : 3 ^ (n - m0) * Nof (n - m0) v M + Sv (padv v) (n - m0) = 2 ^ absv v * M) :
    Nof (n - m0) v M ∉ oddIcc y := by
  intro hmem
  have hNo : Odd (Nof (n - m0) v M) := (Finset.mem_filter.1 hmem).2
  have hw := nof_win hD hv hM (two_pow_mono_M (by omega) (hMk M hM)) hNo.pos h
  rw [show m0 + (n - m0) = n by omega, abs_le] at hw
  refine not_mem_oddIcc_of_log hy hNo.pos ?_ hmem
  rcases hout with h' | h'
  · left; linarith
  · right; linarith

/-- The interior and boundary index windows. -/
noncomputable def IntW (m0 n0 : ℕ) (lo hi : ℝ) : Finset ℕ :=
  (Finset.Icc m0 n0).filter (fun n : ℕ => lo ≤ n * Real.log (4 / 3) ∧ n * Real.log (4 / 3) ≤ hi)

noncomputable def BdW (m0 n0 : ℕ) (lo hi Wt : ℝ) : Finset ℕ :=
  (Finset.Icc m0 n0).filter (fun n : ℕ => ¬ (lo ≤ n * Real.log (4 / 3) ∧ n * Real.log (4 / 3) ≤ hi) ∧
    lo - 2 * Wt ≤ n * Real.log (4 / 3) ∧ n * Real.log (4 / 3) ≤ hi + 2 * Wt)

lemma IntBd_disj (m0 n0 : ℕ) (lo hi Wt : ℝ) : Disjoint (IntW m0 n0 lo hi) (BdW m0 n0 lo hi Wt) :=
  Finset.disjoint_filter.2 (fun _ _ h1 h2 => h2.1 h1)

lemma IntW_two [hCb : Fact CbS] {m0 n0 : ℕ} {lo hi : ℝ} (h2m : 2 * m0 * Real.log (4 / 3) ≤ lo) :
    ∀ n ∈ IntW m0 n0 lo hi, 2 * m0 ≤ n := by
  intro n hn
  have hh : 0 < Real.log (4 / 3) := Real.log_pos (by norm_num)
  have h1 := ((Finset.mem_filter.1 hn).2).1
  have : ((2 * m0 : ℕ) : ℝ) ≤ n := by
    push_cast; exact le_of_mul_le_mul_right (le_trans h2m h1) hh
  exact_mod_cast this

/-- The window hypotheses `hin`/`hout` of `win_y` for `S = oddIcc y`. -/
lemma win_hin [hCb : Fact CbS] {x y W D Wt : ℝ} (hD : 0 ≤ D) (hy : 0 < y)
    (hWt : W + D * Real.log 2 + Real.log 2 ≤ Wt)
    {m0 n0 K Mmax : ℕ} {E : ℕ → Prop} (hm0 : 1 ≤ m0)
    (hMk : ∀ M ∈ MMs x W D m0 Mmax E, 2 * (3 / 2 : ℝ) ^ n0 ≤ M)
    (h2m : 2 * m0 * Real.log (4 / 3) ≤ Real.log y - Real.log x + Wt) :
    ∀ n ∈ IntW m0 n0 (Real.log y - Real.log x + Wt) (alph * Real.log y - Real.log x - Wt),
      ∀ p ∈ AAk D K (n - m0) ×ˢ MMs x W D m0 Mmax E,
      3 ^ (n - m0) * Nof (n - m0) p.1 p.2 + Sv (padv p.1) (n - m0) = 2 ^ absv p.1 * p.2 →
        Nof (n - m0) p.1 p.2 ∈ oddIcc y := by
  intro n hn p hp hc
  have h2 := IntW_two h2m n hn
  obtain ⟨hI, hlo, hhi⟩ := Finset.mem_filter.1 hn
  obtain ⟨-, hn0⟩ := Finset.mem_Icc.1 hI
  obtain ⟨hv, hM⟩ := Finset.mem_product.1 hp
  exact win_in hD hy hWt hm0 hMk h2 hn0 hlo hhi hv hM hc

lemma win_hout {x y W D Wt : ℝ} (hD : 0 ≤ D) (hy : 0 < y)
    (hWt : W + D * Real.log 2 + Real.log 2 ≤ Wt)
    {m0 n0 K Mmax : ℕ} {E : ℕ → Prop}
    (hMk : ∀ M ∈ MMs x W D m0 Mmax E, 2 * (3 / 2 : ℝ) ^ n0 ≤ M) :
    ∀ n ∈ Finset.Icc m0 n0,
      n ∉ IntW m0 n0 (Real.log y - Real.log x + Wt) (alph * Real.log y - Real.log x - Wt) →
      n ∉ BdW m0 n0 (Real.log y - Real.log x + Wt) (alph * Real.log y - Real.log x - Wt) Wt →
      ∀ p ∈ AAk D K (n - m0) ×ˢ MMs x W D m0 Mmax E,
      3 ^ (n - m0) * Nof (n - m0) p.1 p.2 + Sv (padv p.1) (n - m0) = 2 ^ absv p.1 * p.2 →
        Nof (n - m0) p.1 p.2 ∉ oddIcc y := by
  intro n hI hnI hnB p hp hc
  obtain ⟨hn, hn0⟩ := Finset.mem_Icc.1 hI
  have hc1 : ¬ (Real.log y - Real.log x + Wt ≤ n * Real.log (4 / 3) ∧
      n * Real.log (4 / 3) ≤ alph * Real.log y - Real.log x - Wt) := fun h =>
    hnI (Finset.mem_filter.2 ⟨hI, h⟩)
  have hc2 : ¬ (Real.log y - Real.log x + Wt - 2 * Wt ≤ n * Real.log (4 / 3) ∧
      n * Real.log (4 / 3) ≤ alph * Real.log y - Real.log x - Wt + 2 * Wt) := fun h =>
    hnB (Finset.mem_filter.2 ⟨hI, hc1, h⟩)
  have hout : n * Real.log (4 / 3) < Real.log y - Real.log x - Wt ∨
      alph * Real.log y - Real.log x + Wt < n * Real.log (4 / 3) := by
    by_contra hcon
    push_neg at hcon
    exact hc2 ⟨by linarith [hcon.1], by linarith [hcon.2]⟩
  obtain ⟨hv, hM⟩ := Finset.mem_product.1 hp
  exact win_out hD hy hWt hMk hn hn0 hout hv hM hc

end Item6f2

section Item6f3
open Classical

lemma card_filter_window (I : Finset ℕ) (a b h : ℝ) (hh : 0 < h) (ha : 0 ≤ a) (hab : a ≤ b) :
    ((I.filter (fun n : ℕ => a ≤ n * h ∧ n * h ≤ b)).card : ℝ) ≤ (b - a) / h + 1 := by
  have hsub : I.filter (fun n : ℕ => a ≤ n * h ∧ n * h ≤ b) ⊆
      (Finset.range (⌊b / h⌋₊ + 1)).filter (fun n : ℕ => a ≤ n * h ∧ n * h ≤ b) := by
    intro n hn
    obtain ⟨-, h1, h2⟩ := Finset.mem_filter.1 hn
    refine Finset.mem_filter.2 ⟨Finset.mem_range.2 (Nat.lt_succ_of_le (Nat.le_floor ?_)), h1, h2⟩
    rw [le_div_iff₀ hh]; exact h2
  refine le_trans ((Nat.cast_le (α := ℝ)).2 (Finset.card_le_card hsub)) ?_
  refine (card_window _ a b h hh ha hab (fun n h1 h2 => ?_)).2
  refine Finset.mem_range.2 (Nat.lt_succ_of_le (Nat.le_floor ?_))
  rw [le_div_iff₀ hh]; exact h2

lemma IntW_card {m0 n0 : ℕ} {lo hi : ℝ} (hlo0 : 0 ≤ lo) (hlh : lo ≤ hi)
    (hlo : (m0 : ℝ) * Real.log (4 / 3) ≤ lo) (hhi : hi ≤ (n0 : ℝ) * Real.log (4 / 3)) :
    |((IntW m0 n0 lo hi).card : ℝ) - (hi - lo) / Real.log (4 / 3)| ≤ 1 := by
  have hh : 0 < Real.log (4 / 3) := Real.log_pos (by norm_num)
  have hc := card_window (Finset.Icc m0 n0) lo hi _ hh hlo0 hlh (fun n h1 h2 => by
    refine Finset.mem_Icc.2 ⟨?_, ?_⟩
    · exact_mod_cast le_of_mul_le_mul_right (le_trans hlo h1) hh
    · exact_mod_cast le_of_mul_le_mul_right (le_trans h2 hhi) hh)
  unfold IntW
  rw [abs_le]; constructor <;> linarith [hc.1, hc.2]

lemma BdW_card {m0 n0 : ℕ} {lo hi Wt : ℝ} (hW : 0 ≤ Wt) (h2 : 2 * Wt ≤ lo) (hlh : lo ≤ hi) :
    ((BdW m0 n0 lo hi Wt).card : ℝ) ≤ 2 * (2 * Wt / Real.log (4 / 3) + 1) := by
  have hh : 0 < Real.log (4 / 3) := Real.log_pos (by norm_num)
  have hsub : BdW m0 n0 lo hi Wt ⊆
      (Finset.Icc m0 n0).filter (fun n : ℕ => lo - 2 * Wt ≤ n * Real.log (4 / 3) ∧
        n * Real.log (4 / 3) ≤ lo) ∪
      (Finset.Icc m0 n0).filter (fun n : ℕ => hi ≤ n * Real.log (4 / 3) ∧
        n * Real.log (4 / 3) ≤ hi + 2 * Wt) := by
    intro n hn
    obtain ⟨hI, hni, h1, h2'⟩ := Finset.mem_filter.1 hn
    rcases le_or_gt lo (n * Real.log (4 / 3)) with hl | hl
    · have hhi : hi < n * Real.log (4 / 3) := by
        by_contra hc; exact hni ⟨hl, not_lt.1 hc⟩
      exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hI, hhi.le, h2'⟩)
    · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hI, h1, hl.le⟩)
  have c1 := card_filter_window (Finset.Icc m0 n0) (lo - 2 * Wt) lo _ hh (by linarith) (by linarith)
  have c2 := card_filter_window (Finset.Icc m0 n0) hi (hi + 2 * Wt) _ hh (by linarith) (by linarith)
  have hu := le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)
  have hu' : ((BdW m0 n0 lo hi Wt).card : ℝ) ≤
      (((Finset.Icc m0 n0).filter (fun n : ℕ => lo - 2 * Wt ≤ n * Real.log (4 / 3) ∧
        n * Real.log (4 / 3) ≤ lo)).card : ℝ) +
      (((Finset.Icc m0 n0).filter (fun n : ℕ => hi ≤ n * Real.log (4 / 3) ∧
        n * Real.log (4 / 3) ≤ hi + 2 * Wt)).card : ℝ) := by exact_mod_cast hu
  have e1 : (lo - (lo - 2 * Wt)) / Real.log (4 / 3) = 2 * Wt / Real.log (4 / 3) := by ring
  have e2 : (hi + 2 * Wt - hi) / Real.log (4 / 3) = 2 * Wt / Real.log (4 / 3) := by ring
  linarith

end Item6f3

section Item6f4
open Classical

/-- Per-`y` asymptotic (Tao (5.20) for one `y`): `Σ_n P_y(G_n) ≈ 2Λ/h`, `h = log(4/3)`. -/
lemma py_close [hCb : Fact CbS] (y x W D Wt ε H eb : ℝ) (m0 n0 K Mmax : ℕ) (E : ℕ → Prop) (β : ℕ → ℝ)
    (hD : 0 ≤ D) (hy16 : 16 ≤ y) (hgap : y + 1 ≤ y ^ alph)
    (hWt : W + D * Real.log 2 + Real.log 2 ≤ Wt) (hWt0 : 0 ≤ Wt) (hm0 : 1 ≤ m0)
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1) (hH0 : 0 ≤ H)
    (hMM : ∀ M ∈ MMs x W D m0 Mmax E, 2 * (3 / 2 : ℝ) ^ n0 ≤ ε * M)
    (hH : ∀ k ≤ n0, ∀ Y : ZMod (3 ^ k),
      ∑ M ∈ (MMs x W D m0 Mmax E).filter (fun M : ℕ => (M : ZMod (3 ^ k)) = Y),
        (3 : ℝ) ^ k / M ≤ H)
    (hproj : ∀ j Z, proj m0 (m0 + j) (mu (m0 + j) K) Z = mu m0 K Z * β j)
    (h2m : 2 * m0 * Real.log (4 / 3) ≤ Real.log y - Real.log x + Wt)
    (h2W : 2 * Wt ≤ Real.log y - Real.log x + Wt)
    (hlh : Real.log y - Real.log x + Wt ≤ alph * Real.log y - Real.log x - Wt)
    (hhi : alph * Real.log y - Real.log x - Wt ≤ n0 * Real.log (4 / 3))
    (hL : 4 ≤ (alph - 1) * Real.log y) (heb : 0 ≤ eb)
    (he : ∀ n ∈ IntW m0 n0 (Real.log y - Real.log x + Wt) (alph * Real.log y - Real.log x - Wt),
      |β (n - 2 * m0) - 1| *
          |∑ M ∈ MMs x W D m0 Mmax E, (3 : ℝ) ^ m0 / M * mu m0 K (M : ZMod (3 ^ m0))| +
        H * Osc m0 (n - m0) (mu (n - m0) K) +
        H * ∑ v ∈ Box (n - m0) K \ AAk D K (n - m0), ((1 : ℝ) / 2) ^ absv v ≤ eb) :
    |∑ n ∈ Finset.Icc m0 n0, prob y (Gev x W D m0 K Mmax E n) -
        2 * (∑ M ∈ MMs x W D m0 Mmax E, (3 : ℝ) ^ m0 / M * mu m0 K (M : ZMod (3 ^ m0))) /
          Real.log (4 / 3)| ≤
      4 * (ε * ((alph - 1) * Real.log y / Real.log (4 / 3) + 1) * H +
          ((alph - 1) * Real.log y / Real.log (4 / 3) + 1) * eb +
          (1 + ε) * (2 * (2 * Wt / Real.log (4 / 3) + 1)) * H) / ((alph - 1) * Real.log y) +
        (∑ M ∈ MMs x W D m0 Mmax E, (3 : ℝ) ^ m0 / M * mu m0 K (M : ZMod (3 ^ m0))) *
          (4 * ((2 * Wt / Real.log (4 / 3) + 1) + 2 / Real.log (4 / 3)) /
            ((alph - 1) * Real.log y)) := by
  have hh : 0 < Real.log (4 / 3) := Real.log_pos (by norm_num)
  have hy0 : 0 < y := by linarith
  have hΛ0 : 0 ≤ ∑ M ∈ MMs x W D m0 Mmax E, (3 : ℝ) ^ m0 / M * mu m0 K (M : ZMod (3 ^ m0)) :=
    Finset.sum_nonneg (fun M _ =>
      mul_nonneg (div_nonneg (by positivity) (Nat.cast_nonneg _)) (mu_nonneg _ _ _))
  have hMk : ∀ M ∈ MMs x W D m0 Mmax E, 2 * (3 / 2 : ℝ) ^ n0 ≤ M := fun M hM =>
    le_trans (hMM M hM) (mul_le_of_le_one_left (Nat.cast_nonneg M) hε)
  have h0S : 0 ∉ oddIcc y := fun hm => by
    obtain ⟨k, hk⟩ := (Finset.mem_filter.1 hm).2; omega
  have hW := win_y m0 n0 K (AAk D K) (fun k v hv => (Finset.mem_filter.1 hv).1)
    (MMs x W D m0 Mmax E) (oddIcc y) h0S ε H hε0 hε hH0 hMM hH β hproj
    (IntW m0 n0 (Real.log y - Real.log x + Wt) (alph * Real.log y - Real.log x - Wt))
    (BdW m0 n0 (Real.log y - Real.log x + Wt) (alph * Real.log y - Real.log x - Wt) Wt)
    (Finset.filter_subset _ _) (Finset.filter_subset _ _)
    (IntBd_disj m0 n0 _ _ Wt) (IntW_two h2m)
    (win_hin hD hy0 hWt hm0 hMk h2m) (win_hout hD hy0 hWt hMk)
  have hm0h : 0 ≤ (m0 : ℝ) * Real.log (4 / 3) := by positivity
  have hInt := IntW_card (m0 := m0) (n0 := n0) (by linarith) hlh (by linarith) hhi
  have hBd := BdW_card (m0 := m0) (n0 := n0) hWt0 h2W hlh
  have hsplit : (alph * Real.log y - Real.log x - Wt - (Real.log y - Real.log x + Wt)) /
      Real.log (4 / 3) = (alph - 1) * Real.log y / Real.log (4 / 3) -
        2 * Wt / Real.log (4 / 3) := by ring
  rw [hsplit] at hInt
  have hWh : 0 ≤ 2 * Wt / Real.log (4 / 3) := by positivity
  have hc : |((IntW m0 n0 (Real.log y - Real.log x + Wt)
      (alph * Real.log y - Real.log x - Wt)).card : ℝ) - (alph - 1) * Real.log y / Real.log (4 / 3)| ≤
      2 * Wt / Real.log (4 / 3) + 1 := by
    rw [abs_le] at hInt ⊢; constructor <;> linarith [hInt.1, hInt.2]
  have hIle : ((IntW m0 n0 (Real.log y - Real.log x + Wt)
      (alph * Real.log y - Real.log x - Wt)).card : ℝ) ≤
      (alph - 1) * Real.log y / Real.log (4 / 3) + 1 := by
    rw [abs_le] at hInt; linarith [hInt.2]
  have hsum := Finset.sum_le_card_nsmul _ _ _ he
  rw [nsmul_eq_mul] at hsum
  have t1 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hIle hε0) hH0
  have t2 := mul_le_mul_of_nonneg_right hIle heb
  have t3 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hBd (by linarith : (0 : ℝ) ≤ 1 + ε)) hH0
  have hG : |∑ n ∈ Finset.Icc m0 n0, Gsum (n - m0) (AAk D K (n - m0)) (MMs x W D m0 Mmax E) (oddIcc y) -
      ((IntW m0 n0 (Real.log y - Real.log x + Wt) (alph * Real.log y - Real.log x - Wt)).card : ℝ) *
        ∑ M ∈ MMs x W D m0 Mmax E, (3 : ℝ) ^ m0 / M * mu m0 K (M : ZMod (3 ^ m0))| ≤
      ε * ((alph - 1) * Real.log y / Real.log (4 / 3) + 1) * H +
          ((alph - 1) * Real.log y / Real.log (4 / 3) + 1) * eb +
          (1 + ε) * (2 * (2 * Wt / Real.log (4 / 3) + 1)) * H := by
    refine le_trans hW ?_; linarith
  have hZ := Z_asymp hy16 hgap
  rw [show (alph - 1) / 2 * Real.log y = (alph - 1) * Real.log y / 2 by ring] at hZ
  rw [sum_prob_Gev]
  exact P_close _ _ _ _ _ _ _ _ hL hZ hc hΛ0 hh hG

end Item6f4

/-! ## S23: DECOMPOSE item 6f5, hypothesis discharges for `py_close` / `sec5_split` (towards p120). -/
section Item6f5
open Classical

lemma prob_mono_on (y : ℝ) {P Q : ℕ → Prop} (hPQ : ∀ N ∈ oddIcc y, P N → Q N) :
    prob y P ≤ prob y Q := by
  unfold prob
  apply div_le_div_of_nonneg_right _ (Z_nonneg y)
  apply Finset.sum_le_sum; intro N hN
  by_cases hP : P N
  · simp [hP, hPQ N hN hP]
  · by_cases hQ : Q N <;> simp [hP, hQ] <;> positivity

/-- The last valuation before the passage time is `≤ 4D + 2` on the deviation-good event. -/
lemma a_le_of_dev [hCb : Fact CbS] {M m0 : ℕ} {D : ℝ} (hm0 : 1 ≤ m0)
    (hdev : ∀ j ∈ Finset.Icc 1 m0, |(A M j : ℝ) - 2 * j| ≤ 2 * D) :
    (a (syracuseStep^[m0 - 1] M) : ℝ) ≤ 4 * D + 2 := by
  obtain ⟨k, rfl⟩ : ∃ k, m0 = k + 1 := ⟨m0 - 1, by omega⟩
  have h1 := hdev (k + 1) (Finset.mem_Icc.2 ⟨hm0, le_rfl⟩)
  have hD : 0 ≤ D := by
    have := abs_nonneg ((A M (k + 1) : ℝ) - 2 * ((k + 1 : ℕ) : ℝ)); linarith
  have h0 : 2 * (k : ℝ) - 2 * D ≤ A M k := by
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk; simp only [A, Nat.cast_zero]; linarith
    · have := (abs_le.1 (hdev k (Finset.mem_Icc.2 ⟨hk, by omega⟩))).1; linarith
  have hA : (A M (k + 1) : ℝ) = A M k + a (syracuseStep^[k] M) := by
    simp only [A]; push_cast; ring
  have h2 := (abs_le.1 h1).2
  push_cast at h2
  simp only [Nat.add_sub_cancel]
  linarith

/-- Lemma 5.3 instance: the residue-class harmonic sums of `E''` are `≤ 4` (hypothesis `hH` of `py_close`). -/
lemma hH_MMs [hCb : Fact CbS] {x W D : ℝ} {m0 n0 Mmax : ℕ} (E : ℕ → Prop) (hx : 0 < x) (hm0 : 1 ≤ m0) (Dm : ℕ)
    (hDm : 4 * D + 2 ≤ Dm) (hsize : 4 * (3 : ℝ) ^ (n0 + m0) * 2 ^ Dm ≤ x) :
    ∀ k ≤ n0, ∀ Y : ZMod (3 ^ k),
      ∑ M ∈ (MMs x W D m0 Mmax E).filter (fun M : ℕ => (M : ZMod (3 ^ k)) = Y),
        (3 : ℝ) ^ k / M ≤ 4 := by
  intro k hk Y
  have h3 : (3 : ℝ) ^ (k + m0) ≤ 3 ^ (n0 + m0) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hc := c_bound x hx m0 k Dm hm0
    (le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h3 (by norm_num)) (by positivity))
      hsize)
    ((MMs x W D m0 Mmax E).filter (fun M : ℕ => (M : ZMod (3 ^ k)) = Y)) ?_ ?_
  · calc ∑ M ∈ (MMs x W D m0 Mmax E).filter (fun M : ℕ => (M : ZMod (3 ^ k)) = Y), (3 : ℝ) ^ k / M
          = (3 : ℝ) ^ k * ∑ M ∈ (MMs x W D m0 Mmax E).filter
              (fun M : ℕ => (M : ZMod (3 ^ k)) = Y), (1 : ℝ) / M := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun M _ => by ring)
      _ ≤ 4 := hc
  · intro M hM
    obtain ⟨hMs, -⟩ := Finset.mem_filter.1 hM
    obtain ⟨hodd, ⟨hreach, hT, -, -⟩, hdev⟩ := (Finset.mem_filter.1 hMs).2
    refine ⟨hodd, ?_, ?_, ?_⟩
    · have := T_spec x M hreach; rwa [hT] at this
    · exact T_min x M hreach (m0 - 1) (by omega)
    · have := a_le_of_dev hm0 hdev
      exact_mod_cast le_trans this hDm
  · intro M hM M' hM'
    have h1 := (Finset.mem_filter.1 hM).2
    have h2 := (Finset.mem_filter.1 hM').2
    have he : ((M : ℤ) : ZMod (3 ^ k)) = ((M' : ℤ) : ZMod (3 ^ k)) := by
      push_cast; rw [h1, h2]
    have := (ZMod.intCast_eq_intCast_iff_dvd_sub (M : ℤ) (M' : ℤ) (3 ^ k)).1 he
    exact_mod_cast this

/-- Elements of `E''` are `≥ x` (they sit `m0` steps above `x` up to `e^W`, and `W ≤ m0 log(4/3)`). -/
lemma MMs_ge [hCb : Fact CbS] {x W D : ℝ} {m0 Mmax : ℕ} {E : ℕ → Prop} (hx : 0 < x)
    (hWm : W ≤ m0 * Real.log (4 / 3)) {M : ℕ} (hM : M ∈ MMs x W D m0 Mmax E) : x ≤ M := by
  obtain ⟨hodd, ⟨-, -, -, hlog⟩, -⟩ := (Finset.mem_filter.1 hM).2
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hodd.pos
  have h := (abs_le.1 hlog).1
  exact (Real.log_le_log_iff hx hM0).1 (by linarith)

/-- Hypothesis `hMM` of `py_close`. -/
lemma hMM_of [hCb : Fact CbS] {x W D ε : ℝ} {m0 n0 Mmax : ℕ} {E : ℕ → Prop} (hx : 0 < x) (hε : 0 ≤ ε)
    (hWm : W ≤ m0 * Real.log (4 / 3)) (hbig : 2 * (3 / 2 : ℝ) ^ n0 ≤ ε * x) :
    ∀ M ∈ MMs x W D m0 Mmax E, 2 * (3 / 2 : ℝ) ^ n0 ≤ ε * M := fun M hM =>
  le_trans hbig (mul_le_mul_of_nonneg_left (MMs_ge hx hWm hM) hε)

/-- Tao (5.16): on the deviation-good event, the passage time `T_x(N)` of `N ∈ [y, y^α]` lies in `[m0, n0]`. -/
lemma T_range {x y D : ℝ} {N m0 n0 : ℕ} (hD : 0 ≤ D) (hx1 : 1 ≤ x) (hy : 0 < y)
    (hN : N ∈ oddIcc y) (h4 : (4 : ℝ) ^ n0 ≤ y) (hxy : x ≤ y)
    (hdev : ∀ j ∈ Finset.Icc 1 n0, |(A N j : ℝ) - 2 * j| ≤ D)
    (hhi : alph * Real.log y + n0 * Real.log (3 / 4) + (2 * D + 1) * Real.log 2 ≤ Real.log x)
    (hlo : (m0 + 1) * Real.log (4 / 3) + (2 * D + 1) * Real.log 2 ≤ Real.log y - Real.log x) :
    Reaches x N ∧ m0 ≤ T x N ∧ T x N ≤ n0 := by
  obtain ⟨hI, -⟩ := Finset.mem_filter.1 hN
  obtain ⟨hc, hf⟩ := Finset.mem_Icc.1 hI
  have hyN : y ≤ N := le_trans (Nat.le_ceil y) (by exact_mod_cast hc)
  have hNy : (N : ℝ) ≤ y ^ alph :=
    le_trans (by exact_mod_cast hf) (Nat.floor_le (Real.rpow_nonneg hy.le _))
  have hN0 : (0 : ℝ) < N := lt_of_lt_of_le hy hyN
  have hx0 : (0 : ℝ) < x := by linarith
  have hlogN : Real.log N ≤ alph * Real.log y := by
    rw [← Real.log_rpow hy]; exact Real.log_le_log hN0 hNy
  have hlogy : Real.log y ≤ Real.log N := Real.log_le_log hy hyN
  have h43 : 0 < Real.log (4 / 3 : ℝ) := Real.log_pos (by norm_num)
  obtain ⟨hR, hT, hTa⟩ := T_approx hx1 (le_trans hxy hyN)
    (approx_all N n0 D hD (le_trans h4 hyN) hdev) (by linarith)
  refine ⟨hR, ?_, hT⟩
  by_contra hlt
  have hTm : (T x N : ℝ) + 1 ≤ m0 := by exact_mod_cast (show T x N + 1 ≤ m0 by omega)
  rw [Real.log_div hN0.ne' hx0.ne'] at hTa
  have h1 := (abs_le.1 hTa).1
  have h2 : (T x N : ℝ) * Real.log (4 / 3) ≤ ((m0 : ℝ) - 1) * Real.log (4 / 3) :=
    mul_le_mul_of_nonneg_right (by linarith) h43.le
  linarith

/-- The bad event of `sec5_split` reduces to the deviation event (Tao (5.12)) for `y ∈ [x^α, x^{α²}]`. -/
lemma bad_le_dev (y : ℝ) {x D : ℝ} {m0 n0 : ℕ} (hD : 0 ≤ D) (hx1 : 1 ≤ x) (hy : 0 < y)
    (h4 : (4 : ℝ) ^ n0 ≤ y) (hxy : x ≤ y)
    (hhi : alph * Real.log y + n0 * Real.log (3 / 4) + (2 * D + 1) * Real.log 2 ≤ Real.log x)
    (hlo : (m0 + 1) * Real.log (4 / 3) + (2 * D + 1) * Real.log 2 ≤ Real.log y - Real.log x) :
    prob y (fun N => ¬ ((∀ j ∈ Finset.Icc 1 n0, |(A N j : ℝ) - 2 * j| ≤ D) ∧
        (Reaches x N → m0 ≤ T x N ∧ T x N ≤ n0))) ≤
      prob y (fun N => ¬ ∀ j ∈ Finset.Icc 1 n0, |(A N j : ℝ) - 2 * j| ≤ D) := by
  apply prob_mono_on
  intro N hN hbad hdev
  exact hbad ⟨hdev, fun _ => (T_range hD hx1 hy hN h4 hxy hdev hhi hlo).2⟩

/-- Box mass: `Σ_{Box j K} 2^{-|v|} = (1 - 2^{-K})^j`. -/
lemma box_mass_eq (j K : ℕ) :
    ∑ v ∈ Box j K, ((1 : ℝ) / 2) ^ (∑ i, v i) = (1 - (1 / 2) ^ K) ^ j := by
  rw [← geo_one K]
  have hc : (∑ k ∈ Finset.Icc 1 K, ((1 : ℝ) / 2) ^ k) ^ j =
      ∏ _i : Fin j, ∑ k ∈ Finset.Icc 1 K, ((1 : ℝ) / 2) ^ k := by
    simp [Finset.prod_const]
  rw [hc, Finset.prod_univ_sum]
  unfold Box
  refine Finset.sum_congr rfl (fun v _ => ?_)
  rw [Finset.prod_pow_eq_pow_sum]

/-- `|β_j - 1| ≤ j 2^{-K}` for `β_j = Σ_{Box j K} 2^{-|v|}` (the `proj_mu` factor). -/
lemma beta_close (j K : ℕ) :
    |∑ v ∈ Box j K, ((1 : ℝ) / 2) ^ (∑ i, v i) - 1| ≤ j * (1 / 2) ^ K := by
  rw [box_mass_eq]
  have ht0 : (0 : ℝ) ≤ (1 / 2) ^ K := by positivity
  have ht1 : ((1 : ℝ) / 2) ^ K ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hup : (1 - ((1 : ℝ) / 2) ^ K) ^ j ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
  have hlow : 1 - (j : ℝ) * ((1 : ℝ) / 2) ^ K ≤ (1 - ((1 : ℝ) / 2) ^ K) ^ j := by
    have := one_add_mul_le_pow (show (-2 : ℝ) ≤ -((1 : ℝ) / 2) ^ K by linarith) j
    rw [← sub_eq_add_neg] at this
    linarith
  rw [abs_sub_comm, abs_of_nonneg (by linarith)]
  linarith

/-- Bad-box mass of `AAk D` via the Chernoff prefix bound (`dev_bad_mass` of `_syr.lean`, hypothesis `hdevK`). -/
lemma box_bad_le (k K : ℕ) (D C L : ℝ) (hC : 1 ≤ C) (hL : 0 ≤ L)
    (hCL : C * (Real.sqrt (k * L) + L) ≤ D)
    (hdevK : ∑ w ∈ (Box k K).filter (fun w => ¬ DevOK C L (padv w) k),
        ((1 : ℝ) / 2) ^ (∑ i, w i) ≤ 2 * k * Real.exp (-(C * L) / 24)) :
    ∑ v ∈ Box k K \ AAk D K k, ((1 : ℝ) / 2) ^ absv v ≤ 2 * k * Real.exp (-(C * L) / 24) := by
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity)) hdevK
  intro v hv
  obtain ⟨hvB, hvA⟩ := Finset.mem_sdiff.1 hv
  refine Finset.mem_filter.2 ⟨hvB, fun hok => hvA (Finset.mem_filter.2 ⟨hvB, fun j hj => ?_⟩)⟩
  have hjk : (j : ℝ) ≤ k := by exact_mod_cast (Finset.mem_Icc.1 hj).2
  have hs : Real.sqrt (j * L) ≤ Real.sqrt (k * L) :=
    Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hjk hL)
  calc _ ≤ C * (Real.sqrt (j * L) + L) := hok j hj
    _ ≤ C * (Real.sqrt (k * L) + L) := mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    _ ≤ D := hCL

/-- `Λ` of (5.20): the level-`m0` residue-weighted harmonic sum of `E''` (independent of `y`). -/
noncomputable def LamS (x W D : ℝ) (m0 K Mmax : ℕ) (E : ℕ → Prop) : ℝ :=
  ∑ M ∈ MMs x W D m0 Mmax E, (3 : ℝ) ^ m0 / M * mu m0 K (M : ZMod (3 ^ m0))

lemma LamS_nonneg [hCb : Fact CbS] (x W D : ℝ) (m0 K Mmax : ℕ) (E : ℕ → Prop) : 0 ≤ LamS x W D m0 K Mmax E :=
  Finset.sum_nonneg (fun _ _ =>
    mul_nonneg (div_nonneg (by positivity) (Nat.cast_nonneg _)) (mu_nonneg _ _ _))

/-- Hypothesis `he` of `py_close`: per-`n` error from `beta_close`, Prop 1.14 (`hosc`) and `box_bad_le`. -/
lemma he_of [hCb : Fact CbS] {x W D H Cosc A' C L lo hi : ℝ} {m0 n0 K Mmax : ℕ} {E : ℕ → Prop}
    (hH0 : 0 ≤ H) (hm0 : 1 ≤ m0) (hn0K : n0 ≤ K) (h2m : 2 * m0 * Real.log (4 / 3) ≤ lo)
    (hΛ : LamS x W D m0 K Mmax E ≤ H)
    (hosc : ∀ m n : ℕ, 1 ≤ m → m ≤ n → n ≤ K → Osc m n (mu n K) ≤ Cosc * (m : ℝ) ^ (-A'))
    (hC : 1 ≤ C) (hL : 0 ≤ L) (hCL : C * (Real.sqrt (n0 * L) + L) ≤ D)
    (hdevK : ∀ k ≤ n0, ∑ w ∈ (Box k K).filter (fun w => ¬ DevOK C L (padv w) k),
        ((1 : ℝ) / 2) ^ (∑ i, w i) ≤ 2 * k * Real.exp (-(C * L) / 24)) :
    ∀ n ∈ IntW m0 n0 lo hi,
      |(∑ v ∈ Box (n - 2 * m0) K, ((1 : ℝ) / 2) ^ (∑ i, v i)) - 1| * |LamS x W D m0 K Mmax E| +
        H * Osc m0 (n - m0) (mu (n - m0) K) +
        H * ∑ v ∈ Box (n - m0) K \ AAk D K (n - m0), ((1 : ℝ) / 2) ^ absv v ≤
      H * (n0 * (1 / 2) ^ K + Cosc * (m0 : ℝ) ^ (-A') + 2 * n0 * Real.exp (-(C * L) / 24)) := by
  intro n hn
  have hn2 := IntW_two h2m n hn
  have hnn0 : n ≤ n0 := (Finset.mem_Icc.1 (Finset.mem_filter.1 hn).1).2
  have hΛ0 := LamS_nonneg x W D m0 K Mmax E
  have hb := beta_close (n - 2 * m0) K
  have hcast : ((n - 2 * m0 : ℕ) : ℝ) ≤ n0 := by exact_mod_cast (show n - 2 * m0 ≤ n0 by omega)
  have t1 : |(∑ v ∈ Box (n - 2 * m0) K, ((1 : ℝ) / 2) ^ (∑ i, v i)) - 1| *
      |LamS x W D m0 K Mmax E| ≤ ((n0 : ℝ) * (1 / 2) ^ K) * H := by
    rw [abs_of_nonneg hΛ0]
    exact mul_le_mul (le_trans hb (mul_le_mul_of_nonneg_right hcast (by positivity))) hΛ hΛ0
      (by positivity)
  have t2 : Osc m0 (n - m0) (mu (n - m0) K) ≤ Cosc * (m0 : ℝ) ^ (-A') :=
    hosc m0 (n - m0) hm0 (by omega) (by omega)
  have hk : ((n - m0 : ℕ) : ℝ) ≤ n0 := by exact_mod_cast (show n - m0 ≤ n0 by omega)
  have hCL' : C * (Real.sqrt ((n - m0 : ℕ) * L) + L) ≤ D := by
    have := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hk hL)
    exact le_trans (mul_le_mul_of_nonneg_left (by linarith) (by linarith)) hCL
  have t3 := box_bad_le (n - m0) K D C L hC hL hCL' (hdevK (n - m0) (by omega))
  have t3' : 2 * ((n - m0 : ℕ) : ℝ) * Real.exp (-(C * L) / 24) ≤
      2 * n0 * Real.exp (-(C * L) / 24) := by
    have := mul_le_mul_of_nonneg_right hk (Real.exp_pos (-(C * L) / 24)).le
    linarith
  have u2 := mul_le_mul_of_nonneg_left t2 hH0
  have u3 := mul_le_mul_of_nonneg_left (le_trans t3 t3') hH0
  (first | linarith | nlinarith)

/-- Tao (5.20) for one `y`, explicit parameters: `P_y(Reaches ∧ E(Pass)) = 2Λ/log(4/3) + error`,
error = deviation probability (bounded by `p512`) + `py_close` error with `H = 4`. -/
lemma p120_y [hCb : Fact CbS] (y : ℝ) {x W D Wt ε C L Cosc A' : ℝ} {m0 n0 K Mmax Dm : ℕ} (E : ℕ → Prop)
    (hx1 : 1 ≤ x) (hD : 0 ≤ D) (hm0 : 1 ≤ m0) (hmn : m0 ≤ n0) (hy16 : 16 ≤ y) (hxy : x ≤ y)
    (hgap : y + 1 ≤ y ^ alph)
    (hW : 2 * ((2 * D + 1) * Real.log 2) + Real.log (4 / 3) ≤ W)
    (hWm : W + 2 * ((2 * D + 1) * Real.log 2) < m0 * Real.log (4 / 3))
    (hK : 2 * (n0 : ℝ) + D ≤ K)
    (hMmax : Real.exp (Real.log x + m0 * Real.log (4 / 3) + W) < Mmax)
    (h4 : (4 : ℝ) ^ n0 ≤ y)
    (hhi' : alph * Real.log y + n0 * Real.log (3 / 4) + (2 * D + 1) * Real.log 2 ≤ Real.log x)
    (hlo' : (m0 + 1) * Real.log (4 / 3) + (2 * D + 1) * Real.log 2 ≤ Real.log y - Real.log x)
    (hWt : W + D * Real.log 2 + Real.log 2 ≤ Wt) (hWt0 : 0 ≤ Wt) (hε0 : 0 ≤ ε) (hε : ε ≤ 1)
    (hbig : 2 * (3 / 2 : ℝ) ^ n0 ≤ ε * x)
    (hDm : 4 * D + 2 ≤ Dm) (hsize : 4 * (3 : ℝ) ^ (n0 + m0) * 2 ^ Dm ≤ x)
    (hproj : ∀ j Z, proj m0 (m0 + j) (mu (m0 + j) K) Z =
      mu m0 K Z * ∑ v ∈ Box j K, ((1 : ℝ) / 2) ^ (∑ i, v i))
    (h2m : 2 * m0 * Real.log (4 / 3) ≤ Real.log y - Real.log x + Wt)
    (h2W : 2 * Wt ≤ Real.log y - Real.log x + Wt)
    (hlh : Real.log y - Real.log x + Wt ≤ alph * Real.log y - Real.log x - Wt)
    (hhi : alph * Real.log y - Real.log x - Wt ≤ n0 * Real.log (4 / 3))
    (hL4 : 4 ≤ (alph - 1) * Real.log y)
    (hCosc : 0 ≤ Cosc)
    (hosc : ∀ m n : ℕ, 1 ≤ m → m ≤ n → n ≤ K → Osc m n (mu n K) ≤ Cosc * (m : ℝ) ^ (-A'))
    (hC : 1 ≤ C) (hL : 0 ≤ L) (hCL : C * (Real.sqrt (n0 * L) + L) ≤ D)
    (hdevK : ∀ k ≤ n0, ∑ w ∈ (Box k K).filter (fun w => ¬ DevOK C L (padv w) k),
        ((1 : ℝ) / 2) ^ (∑ i, w i) ≤ 2 * k * Real.exp (-(C * L) / 24)) :
    |prob y (fun N => Reaches x N ∧ E (Pass x N)) - 2 * LamS x W D m0 K Mmax E / Real.log (4 / 3)| ≤
      prob y (fun N => ¬ ∀ j ∈ Finset.Icc 1 n0, |(A N j : ℝ) - 2 * j| ≤ D) +
      (4 * (ε * ((alph - 1) * Real.log y / Real.log (4 / 3) + 1) * 4 +
          ((alph - 1) * Real.log y / Real.log (4 / 3) + 1) *
            (4 * (n0 * (1 / 2) ^ K + Cosc * (m0 : ℝ) ^ (-A') + 2 * n0 * Real.exp (-(C * L) / 24))) +
          (1 + ε) * (2 * (2 * Wt / Real.log (4 / 3) + 1)) * 4) / ((alph - 1) * Real.log y) +
        LamS x W D m0 K Mmax E *
          (4 * ((2 * Wt / Real.log (4 / 3) + 1) + 2 / Real.log (4 / 3)) /
            ((alph - 1) * Real.log y))) := by
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := by linarith
  have hl2 : 0 ≤ (2 * D + 1) * Real.log 2 := mul_nonneg (by linarith) (Real.log_nonneg (by norm_num))
  have hH := hH_MMs (W := W) (D := D) (Mmax := Mmax) E hx0 hm0 Dm hDm hsize
  have hWm' : W ≤ m0 * Real.log (4 / 3) := by linarith
  have hMM := hMM_of (D := D) (Mmax := Mmax) (E := E) hx0 hε0 hWm' hbig
  have hΛ : LamS x W D m0 K Mmax E ≤ 4 := Lam_le_H m0 K _ 4 (by norm_num) (hH m0 hmn)
  have hn0K : n0 ≤ K := by
    have : (n0 : ℝ) ≤ K := by linarith
    exact_mod_cast this
  have hhe := he_of (lo := Real.log y - Real.log x + Wt) (hi := alph * Real.log y - Real.log x - Wt)
    (by norm_num : (0 : ℝ) ≤ 4) hm0 hn0K h2m hΛ hosc hC hL hCL hdevK
  have heb : (0 : ℝ) ≤ 4 * (n0 * (1 / 2) ^ K + Cosc * (m0 : ℝ) ^ (-A') +
      2 * n0 * Real.exp (-(C * L) / 24)) := by
    have : 0 ≤ Cosc * (m0 : ℝ) ^ (-A') := mul_nonneg hCosc (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    have : (0 : ℝ) ≤ n0 * (1 / 2) ^ K := by positivity
    have : (0 : ℝ) ≤ 2 * n0 * Real.exp (-(C * L) / 24) := by positivity
    linarith
  have h5 := sec5_split y E hx0 hD hm0 hW hWm hK hMmax h4
  have hb := bad_le_dev y (m0 := m0) hD hx1 hy0 h4 hxy hhi' hlo'
  have hp := py_close y x W D Wt ε 4 _ m0 n0 K Mmax E
    (fun j => ∑ v ∈ Box j K, ((1 : ℝ) / 2) ^ (∑ i, v i)) hD hy16 hgap hWt hWt0 hm0 hε0 hε
    (by norm_num) hMM hH hproj h2m h2W hlh hhi hL4 heb hhe
  unfold LamS
  exact le_trans (abs_sub_le _ (∑ n ∈ Finset.Icc m0 n0, prob y (Gev x W D m0 K Mmax E n)) _)
    (add_le_add (h5.trans hb) hp)

end Item6f5


section Num120

/-! Parameters of Tao (5.20) as functions of `x` (log x = u^5). -/
noncomputable def pn0 (x : ℝ) : ℕ := ⌊Real.log x / (10 * Real.log 2)⌋₊
noncomputable def pD (x : ℝ) : ℝ := 2 * Real.log x ^ ((3 : ℝ) / 5)
noncomputable def pL (x : ℝ) : ℝ := Real.log x ^ ((1 : ℝ) / 5)
noncomputable def pW (x : ℝ) : ℝ := 2 * ((2 * pD x + 1) * Real.log 2) + Real.log (4 / 3)
noncomputable def pm0 (x : ℝ) : ℕ :=
  ⌈(pW x + 2 * ((2 * pD x + 1) * Real.log 2) + 1) / Real.log (4 / 3)⌉₊
noncomputable def pWt (x : ℝ) : ℝ := pW x + pD x * Real.log 2 + Real.log 2
noncomputable def pK (x : ℝ) : ℕ := ⌈2 * (pn0 x : ℝ) + pD x⌉₊
noncomputable def pMmax (x : ℝ) : ℕ :=
  ⌊Real.exp (Real.log x + pm0 x * Real.log (4 / 3) + pW x)⌋₊ + 1
noncomputable def peps (x : ℝ) : ℝ := 2 * (3 / 2 : ℝ) ^ (pn0 x) / x
noncomputable def pDm (x : ℝ) : ℕ := ⌈4 * pD x + 2⌉₊

/-- The six numerical estimates of the parameter choices (proved in a separate child). -/
def NumS : Prop :=
  (∀ (x u : ℝ) (hu : 1000 ≤ u) (hx0 : 0 < x) (hx : Real.log x = u ^ 5),
      1 ≤ x ∧ 0 ≤ pD x ∧ pD x = 2 * u ^ 3 ∧ pL x = u ∧ 1000000 * u ^ 3 ≤ Real.log x ∧
    u ≤ u ^ 3 ∧ 6.931 * (pn0 x : ℝ) ≤ Real.log x ∧ Real.log x ≤ 6.932 * ((pn0 x : ℝ) + 1) ∧
    0 ≤ pW x ∧ pW x ≤ 6 * u ^ 3 ∧ 0 ≤ pWt x ∧ pWt x ≤ 8 * u ^ 3 ∧
    pW x + 2 * ((2 * pD x + 1) * Real.log 2) + 1 ≤ pm0 x * Real.log (4 / 3) ∧
    (pm0 x : ℝ) * Real.log (4 / 3) ≤ 13 * u ^ 3 ∧ (pm0 x : ℝ) ≤ 52 * u ^ 3 ∧ 1 ≤ pm0 x ∧
    u ≤ (pm0 x : ℝ) ∧ 2 * (pn0 x : ℝ) + pD x ≤ pK x ∧
    4 * pD x + 2 ≤ pDm x ∧ (pDm x : ℝ) ≤ 8 * u ^ 3 + 3) ∧
  (∀ (x u : ℝ) (hu : 1000 ≤ u) (hx0 : 0 < x) (hx : Real.log x = u ^ 5),
      0 ≤ peps x ∧ peps x * u ≤ 1 ∧ peps x ≤ 1 ∧ 2 * (3 / 2 : ℝ) ^ (pn0 x) ≤ peps x * x ∧
    4 * (3 : ℝ) ^ (pn0 x + pm0 x) * 2 ^ (pDm x) ≤ x ∧
    1 * (Real.sqrt (pn0 x * pL x) + pL x) ≤ pD x ∧ pm0 x ≤ pn0 x) ∧
  (∀ (x u a : ℝ) (hu : 1000 ≤ u) (hx0 : 0 < x) (hx : Real.log x = u ^ 5) (ha1 : 1001 / 1000 ≤ a) (ha2 : a ≤ 1002001 / 1000000),
      16 ≤ x ^ a ∧ x ≤ x ^ a ∧ x ^ a + 1 ≤ (x ^ a) ^ alph ∧ (4 : ℝ) ^ (pn0 x) ≤ x ^ a ∧
    alph * Real.log (x ^ a) + pn0 x * Real.log (3 / 4) + (2 * pD x + 1) * Real.log 2 ≤ Real.log x ∧
    (pm0 x + 1) * Real.log (4 / 3) + (2 * pD x + 1) * Real.log 2 ≤ Real.log (x ^ a) - Real.log x ∧
    2 * pm0 x * Real.log (4 / 3) ≤ Real.log (x ^ a) - Real.log x + pWt x ∧
    2 * pWt x ≤ Real.log (x ^ a) - Real.log x + pWt x ∧
    Real.log (x ^ a) - Real.log x + pWt x ≤ alph * Real.log (x ^ a) - Real.log x - pWt x ∧
    alph * Real.log (x ^ a) - Real.log x - pWt x ≤ pn0 x * Real.log (4 / 3) ∧
    4 ≤ (alph - 1) * Real.log (x ^ a)) ∧
  (∀ (ε eb Wt Λ ly h u : ℝ) (hu : 1000 ≤ u) (hly : u ^ 5 / 1000 ≤ ly) (hε0 : 0 ≤ ε) (hεu : ε * u ≤ 1) (hε1 : ε ≤ 1) (heb : 0 ≤ eb) (hWt0 : 0 ≤ Wt) (hWt : Wt ≤ 8 * u ^ 3) (hΛ0 : 0 ≤ Λ) (hΛ : Λ ≤ 4) (ha : 1 / 4 ≤ h) (hb : h ≤ 1 / 3),
      (4 * (ε * (ly / h + 1) * 4 + (ly / h + 1) * eb + (1 + ε) * (2 * (2 * Wt / h + 1)) * 4) / ly +
      Λ * (4 * ((2 * Wt / h + 1) + 2 / h) / ly)) ≤ 5500 / u + 20 * eb) ∧
  (∀ (x u Cosc : ℝ) (hu : 1000 ≤ u) (hx0 : 0 < x) (hx : Real.log x = u ^ 5) (hCosc : 0 ≤ Cosc),
      4 * ((pn0 x : ℝ) * (1 / 2) ^ (pK x) + Cosc * (pm0 x : ℝ) ^ (-(1 : ℝ)) +
      2 * pn0 x * Real.exp (-(1 * pL x) / 24)) ≤ 4 * (1 + Cosc + 2 * 137594142720) / u) ∧
  (∀ (x u : ℝ) (hu : 1000 ≤ u) (hx0 : 0 < x) (hx : Real.log x = u ^ 5),
      8 * x ^ (-(1 / 20000 : ℝ)) + 2 * Real.log x * Real.exp (-(Real.log x ^ ((1 : ℝ) / 5)) / 24) ≤
      (8 + 2 * 137594142720) / u)


lemma h_bd : 1 / 4 ≤ Real.log (4 / 3) ∧ Real.log (4 / 3) ≤ 1 / 3 := by
  constructor
  · have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 4 / 3)
    have e : (1 : ℝ) - (4 / 3)⁻¹ = 1 / 4 := by norm_num
    rw [e] at h; exact h
  · have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4 / 3)
    linarith

/-- Linear bounds on the parameters (atoms `U = log x`, `v = u^3`). -/
lemma num_x [hNS : Fact NumS] (x u : ℝ) (hu : 1000 ≤ u) (hx0 : 0 < x) (hx : Real.log x = u ^ 5) :
    1 ≤ x ∧ 0 ≤ pD x ∧ pD x = 2 * u ^ 3 ∧ pL x = u ∧ 1000000 * u ^ 3 ≤ Real.log x ∧
    u ≤ u ^ 3 ∧ 6.931 * (pn0 x : ℝ) ≤ Real.log x ∧ Real.log x ≤ 6.932 * ((pn0 x : ℝ) + 1) ∧
    0 ≤ pW x ∧ pW x ≤ 6 * u ^ 3 ∧ 0 ≤ pWt x ∧ pWt x ≤ 8 * u ^ 3 ∧
    pW x + 2 * ((2 * pD x + 1) * Real.log 2) + 1 ≤ pm0 x * Real.log (4 / 3) ∧
    (pm0 x : ℝ) * Real.log (4 / 3) ≤ 13 * u ^ 3 ∧ (pm0 x : ℝ) ≤ 52 * u ^ 3 ∧ 1 ≤ pm0 x ∧
    u ≤ (pm0 x : ℝ) ∧ 2 * (pn0 x : ℝ) + pD x ≤ pK x ∧
    4 * pD x + 2 ≤ pDm x ∧ (pDm x : ℝ) ≤ 8 * u ^ 3 + 3 :=
  hNS.out.1 x u hu hx0 hx

/-- `ε`, `hsize`, `hCL`, `m0 ≤ n0`. -/
lemma num_x2 [hCb : Fact CbS] [hNS : Fact NumS] (x u : ℝ) (hu : 1000 ≤ u) (hx0 : 0 < x) (hx : Real.log x = u ^ 5) :
    0 ≤ peps x ∧ peps x * u ≤ 1 ∧ peps x ≤ 1 ∧ 2 * (3 / 2 : ℝ) ^ (pn0 x) ≤ peps x * x ∧
    4 * (3 : ℝ) ^ (pn0 x + pm0 x) * 2 ^ (pDm x) ≤ x ∧
    1 * (Real.sqrt (pn0 x * pL x) + pL x) ≤ pD x ∧ pm0 x ≤ pn0 x :=
  hNS.out.2.1 x u hu hx0 hx

/-- The `y`-dependent hypotheses of `p120_y` at `y = x^a`, `α ≤ a ≤ α²`. -/
lemma num_y [hCb : Fact CbS] [hNS : Fact NumS] (x u a : ℝ) (hu : 1000 ≤ u) (hx0 : 0 < x) (hx : Real.log x = u ^ 5) (ha1 : 1001 / 1000 ≤ a) (ha2 : a ≤ 1002001 / 1000000) :
    16 ≤ x ^ a ∧ x ≤ x ^ a ∧ x ^ a + 1 ≤ (x ^ a) ^ alph ∧ (4 : ℝ) ^ (pn0 x) ≤ x ^ a ∧
    alph * Real.log (x ^ a) + pn0 x * Real.log (3 / 4) + (2 * pD x + 1) * Real.log 2 ≤ Real.log x ∧
    (pm0 x + 1) * Real.log (4 / 3) + (2 * pD x + 1) * Real.log 2 ≤ Real.log (x ^ a) - Real.log x ∧
    2 * pm0 x * Real.log (4 / 3) ≤ Real.log (x ^ a) - Real.log x + pWt x ∧
    2 * pWt x ≤ Real.log (x ^ a) - Real.log x + pWt x ∧
    Real.log (x ^ a) - Real.log x + pWt x ≤ alph * Real.log (x ^ a) - Real.log x - pWt x ∧
    alph * Real.log (x ^ a) - Real.log x - pWt x ≤ pn0 x * Real.log (4 / 3) ∧
    4 ≤ (alph - 1) * Real.log (x ^ a) :=
  hNS.out.2.2.1 x u a hu hx0 hx ha1 ha2

/-- The `py_close` error of `p120_y`, with the parameters plugged in, is `≤ 5500/u + 20 eb`. -/
lemma err_gen [hCb : Fact CbS] [hNS : Fact NumS] (ε eb Wt Λ ly h u : ℝ) (hu : 1000 ≤ u) (hly : u ^ 5 / 1000 ≤ ly) (hε0 : 0 ≤ ε) (hεu : ε * u ≤ 1) (hε1 : ε ≤ 1) (heb : 0 ≤ eb) (hWt0 : 0 ≤ Wt) (hWt : Wt ≤ 8 * u ^ 3) (hΛ0 : 0 ≤ Λ) (hΛ : Λ ≤ 4) (ha : 1 / 4 ≤ h) (hb : h ≤ 1 / 3) :
    (4 * (ε * (ly / h + 1) * 4 + (ly / h + 1) * eb + (1 + ε) * (2 * (2 * Wt / h + 1)) * 4) / ly +
      Λ * (4 * ((2 * Wt / h + 1) + 2 / h) / ly)) ≤ 5500 / u + 20 * eb :=
  hNS.out.2.2.2.1 ε eb Wt Λ ly h u hu hly hε0 hεu hε1 heb hWt0 hWt hΛ0 hΛ ha hb

/-- `eb` of `p120_y` with the parameters plugged in (`C = 1`, `A' = 1`, `L = u`). -/
lemma eb_bound [hNS : Fact NumS] (x u Cosc : ℝ) (hu : 1000 ≤ u) (hx0 : 0 < x) (hx : Real.log x = u ^ 5) (hCosc : 0 ≤ Cosc) :
    4 * ((pn0 x : ℝ) * (1 / 2) ^ (pK x) + Cosc * (pm0 x : ℝ) ^ (-(1 : ℝ)) +
      2 * pn0 x * Real.exp (-(1 * pL x) / 24)) ≤ 4 * (1 + Cosc + 2 * 137594142720) / u :=
  hNS.out.2.2.2.2.1 x u Cosc hu hx0 hx hCosc

/-- The `p512` deviation bound is `≤ (8 + 2 B)/u`. -/
lemma dev_bound [hNS : Fact NumS] (x u : ℝ) (hu : 1000 ≤ u) (hx0 : 0 < x) (hx : Real.log x = u ^ 5) :
    8 * x ^ (-(1 / 20000 : ℝ)) + 2 * Real.log x * Real.exp (-(Real.log x ^ ((1 : ℝ) / 5)) / 24) ≤
      (8 + 2 * 137594142720) / u :=
  hNS.out.2.2.2.2.2 x u hu hx0 hx

end Num120


section P120
variable [hNS : Fact NumS]
include hNS
open Classical

/-- One threshold `y = x^a` of Tao (5.6): the event probability is within `C/u` of `2 Λ / log(4/3)`. -/
lemma p120_one [hCb : Fact CbS]
    (h19 : ∀ (y : ℝ) (n : ℕ), 1 ≤ n → 2 * 2 ^ (3 * n) ≤ ⌈y⌉₊ → 0 < Z y →
      ∀ E : (Fin n → ℕ) → Prop,
      |prob y (fun N => E (vecn n N)) - ∑ v ∈ (Tset n).filter E, ((1 : ℝ) / 2) ^ absv v| ≤
        (2 * (2 ^ (6 * n + 1) / ((⌈y⌉₊ : ℝ) * Z y)) + 2) * (8 / 9) ^ n)
    (hdev : ∀ (n : ℕ) (C L : ℝ), 1 ≤ C → 0 ≤ L →
      ∑ w ∈ (Box n (3 * n)).filter (fun w => ¬ DevOK C L (padv w) n),
        ((1 : ℝ) / 2) ^ (∑ i, w i) ≤ 2 * n * Real.exp (-(C * L) / 24))
    (hdevK : ∀ (n K : ℕ) (C L : ℝ), 1 ≤ C → 0 ≤ L →
      ∑ w ∈ (Box n K).filter (fun w => ¬ DevOK C L (padv w) n),
        ((1 : ℝ) / 2) ^ (∑ i, w i) ≤ 2 * n * Real.exp (-(C * L) / 24))
    (hproj : ∀ (m j K : ℕ) (Z : ZMod (3 ^ m)), proj m (m + j) (mu (m + j) K) Z =
      mu m K Z * ∑ v ∈ Box j K, ((1 : ℝ) / 2) ^ (∑ i, v i))
    (Cosc : ℝ) (hCosc : 0 ≤ Cosc)
    (hosc : ∀ m n K : ℕ, 1 ≤ m → m ≤ n → n ≤ K → Osc m n (mu n K) ≤ Cosc * (m : ℝ) ^ (-(1 : ℝ)))
    (x u a : ℝ) (hu : 1000 ≤ u) (hx0 : 0 < x) (hx : Real.log x = u ^ 5)
    (ha1 : 1001 / 1000 ≤ a) (ha2 : a ≤ 1002001 / 1000000) (E : ℕ → Prop) :
    |prob (x ^ a) (fun N => Reaches x N ∧ E (Pass x N)) -
        2 * LamS x (pW x) (pD x) (pm0 x) (pK x) (pMmax x) E / Real.log (4 / 3)| ≤
      ((8 + 2 * 137594142720) + 5500 + 80 * (1 + Cosc + 2 * 137594142720)) / u := by
  obtain ⟨hx1, hD0, -, hLu, -, -, -, -, -, -, hWt0, hWt8, hWm1, -, -, hm0, -, hK, hDm, -⟩ :=
    num_x x u hu hx0 hx
  obtain ⟨hε0, hεu, hε1, hbig, hsize, hCL, hmn⟩ := num_x2 x u hu hx0 hx
  obtain ⟨hy16, hxy, hgap, h4, hhi', hlo', h2m, h2W, hlh, hhi, hL4⟩ := num_y x u a hu hx0 hx ha1 ha2
  have hL0 : 0 ≤ pL x := by rw [hLu]; linarith
  have hp := p120_y (x ^ a) (x := x) (W := pW x) (D := pD x) (Wt := pWt x) (ε := peps x) (C := 1)
    (L := pL x) (Cosc := Cosc) (A' := 1) (m0 := pm0 x) (n0 := pn0 x) (K := pK x) (Mmax := pMmax x)
    (Dm := pDm x) E hx1 hD0 hm0 hmn hy16 hxy hgap (by unfold pW; exact le_rfl) (by linarith) hK
    (by unfold pMmax; push_cast; exact Nat.lt_floor_add_one _) h4 hhi' hlo'
    (by unfold pWt; exact le_rfl) hWt0 hε0 hε1 hbig hDm hsize (fun j Z => hproj _ j _ Z)
    h2m h2W hlh hhi hL4 hCosc (fun m n hm hmn' hnK => hosc m n _ hm hmn' hnK) le_rfl hL0 hCL
    (fun k _ => hdevK k _ 1 (pL x) le_rfl hL0)
  -- deviation term (Prop 5.12 / p512)
  have hu0 : (0 : ℝ) ≤ u := by linarith
  have hx6 : Real.exp 6000 ≤ x := by
    rw [← Real.exp_log hx0]; apply Real.exp_le_exp.mpr; rw [hx]
    have : (1000 : ℝ) ^ 5 ≤ u ^ 5 := pow_le_pow_left₀ (by norm_num) hu 5
    linarith
  have hyx : x ^ a ≤ x ^ (alph ^ 2) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by unfold alph; linarith)
  have hd : prob (x ^ a) (fun N => ¬ ∀ j ∈ Finset.Icc 1 (pn0 x), |(A N j : ℝ) - 2 * j| ≤ pD x) ≤
      8 * x ^ (-(1 / 20000 : ℝ)) + 2 * Real.log x * Real.exp (-(Real.log x ^ ((1 : ℝ) / 5)) / 24) :=
    p512 h19 hdev x hx6 (x ^ a) hxy hyx
  have hdb := dev_bound x u hu hx0 hx
  -- error term
  have hH := hH_MMs (W := pW x) (D := pD x) (Mmax := pMmax x) E hx0 hm0 (pDm x) hDm hsize
  have hΛ : LamS x (pW x) (pD x) (pm0 x) (pK x) (pMmax x) E ≤ 4 :=
    Lam_le_H (pm0 x) (pK x) _ 4 (by norm_num) (hH (pm0 x) hmn)
  have heb : (0 : ℝ) ≤ 4 * ((pn0 x : ℝ) * (1 / 2) ^ (pK x) + Cosc * (pm0 x : ℝ) ^ (-(1 : ℝ)) +
      2 * pn0 x * Real.exp (-(1 * pL x) / 24)) := by
    have : 0 ≤ Cosc * (pm0 x : ℝ) ^ (-(1 : ℝ)) :=
      mul_nonneg hCosc (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    have : (0 : ℝ) ≤ (pn0 x : ℝ) * (1 / 2) ^ (pK x) := by positivity
    have : (0 : ℝ) ≤ 2 * pn0 x * Real.exp (-(1 * pL x) / 24) := by positivity
    linarith
  have hly : u ^ 5 / 1000 ≤ (alph - 1) * Real.log (x ^ a) := by
    rw [Real.log_rpow hx0, hx]; unfold alph
    have h5 : 0 ≤ u ^ 5 := by positivity
    (first | linarith [mul_nonneg (by linarith : (0 : ℝ) ≤ a - 1) h5] | nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ a - 1) h5])
  have herr := err_gen (peps x) _ (pWt x) (LamS x (pW x) (pD x) (pm0 x) (pK x) (pMmax x) E)
    ((alph - 1) * Real.log (x ^ a)) (Real.log (4 / 3)) u hu hly hε0 hεu hε1 heb hWt0 hWt8
    (LamS_nonneg _ _ _ _ _ _ _) hΛ h_bd.1 h_bd.2
  have hebb := eb_bound x u Cosc hu hx0 hx hCosc
  have hu' : 0 < u := by linarith
  have e1 : ((8 + 2 * 137594142720) + 5500 + 80 * (1 + Cosc + 2 * 137594142720)) / u =
      (8 + 2 * 137594142720) / u + (5500 / u + 20 * (4 * (1 + Cosc + 2 * 137594142720) / u)) := by
    field_simp; ring
  rw [e1]
  refine hp.trans (add_le_add (hd.trans hdb) (herr.trans ?_))
  linarith

/-- Tao (1.20) in event form, from Prop 1.9 (`h19`), the deviation bounds, `proj_mu` and
Prop 1.14 at `A = 1` (`hosc`). -/
theorem p120 [hCb : Fact CbS]
    (h19 : ∀ (y : ℝ) (n : ℕ), 1 ≤ n → 2 * 2 ^ (3 * n) ≤ ⌈y⌉₊ → 0 < Z y →
      ∀ E : (Fin n → ℕ) → Prop,
      |prob y (fun N => E (vecn n N)) - ∑ v ∈ (Tset n).filter E, ((1 : ℝ) / 2) ^ absv v| ≤
        (2 * (2 ^ (6 * n + 1) / ((⌈y⌉₊ : ℝ) * Z y)) + 2) * (8 / 9) ^ n)
    (hdev : ∀ (n : ℕ) (C L : ℝ), 1 ≤ C → 0 ≤ L →
      ∑ w ∈ (Box n (3 * n)).filter (fun w => ¬ DevOK C L (padv w) n),
        ((1 : ℝ) / 2) ^ (∑ i, w i) ≤ 2 * n * Real.exp (-(C * L) / 24))
    (hdevK : ∀ (n K : ℕ) (C L : ℝ), 1 ≤ C → 0 ≤ L →
      ∑ w ∈ (Box n K).filter (fun w => ¬ DevOK C L (padv w) n),
        ((1 : ℝ) / 2) ^ (∑ i, w i) ≤ 2 * n * Real.exp (-(C * L) / 24))
    (hproj : ∀ (m j K : ℕ) (Z : ZMod (3 ^ m)), proj m (m + j) (mu (m + j) K) Z =
      mu m K Z * ∑ v ∈ Box j K, ((1 : ℝ) / 2) ^ (∑ i, v i))
    (hosc : ∃ Cosc : ℝ, 0 ≤ Cosc ∧ ∀ m n K : ℕ, 1 ≤ m → m ≤ n → n ≤ K →
      Osc m n (mu n K) ≤ Cosc * (m : ℝ) ^ (-(1 : ℝ))) :
    ∃ C x0 : ℝ, 0 < C ∧ ∀ x : ℝ, x0 ≤ x → ∀ E : ℕ → Prop,
      |prob (x ^ alph) (fun N => Reaches x N ∧ E (Pass x N)) -
        prob (x ^ (alph ^ 2)) (fun N => Reaches x N ∧ E (Pass x N))| ≤
        C * Real.log x ^ (-((1 : ℝ) / 5)) := by
  obtain ⟨Cosc, hCosc, hosc'⟩ := hosc
  refine ⟨2 * ((8 + 2 * 137594142720) + 5500 + 80 * (1 + Cosc + 2 * 137594142720)),
    Real.exp (1000 ^ 5), by positivity, ?_⟩
  intro x hx E
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx
  have hlx : (1000 : ℝ) ^ 5 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le hx0]; exact hx
  have hl0 : 0 ≤ Real.log x := le_trans (by norm_num) hlx
  set u := Real.log x ^ ((1 : ℝ) / 5) with hu_def
  have hu5 : Real.log x = u ^ 5 := by
    rw [hu_def, ← Real.rpow_natCast, ← Real.rpow_mul hl0]; norm_num
  have hu : 1000 ≤ u := by
    by_contra h; push_neg at h
    have : u ^ 5 < (1000 : ℝ) ^ 5 :=
      pow_lt_pow_left₀ h (Real.rpow_nonneg hl0 _) (by norm_num)
    linarith
  have h1 := p120_one h19 hdev hdevK hproj Cosc hCosc hosc' x u alph hu hx0 hu5
    (by unfold alph; norm_num) (by unfold alph; norm_num) E
  have h2 := p120_one h19 hdev hdevK hproj Cosc hCosc hosc' x u (alph ^ 2) hu hx0 hu5
    (by unfold alph; norm_num) (by unfold alph; norm_num) E
  have hneg : Real.log x ^ (-((1 : ℝ) / 5)) = u⁻¹ := by
    rw [Real.rpow_neg hl0]
  rw [hneg]
  have hu' : 0 < u := by linarith
  have e : 2 * ((8 + 2 * 137594142720) + 5500 + 80 * (1 + Cosc + 2 * 137594142720)) * u⁻¹ =
      ((8 + 2 * 137594142720) + 5500 + 80 * (1 + Cosc + 2 * 137594142720)) / u +
      ((8 + 2 * 137594142720) + 5500 + 80 * (1 + Cosc + 2 * 137594142720)) / u := by
    field_simp; ring
  rw [e]
  refine (abs_sub_le _ (2 * LamS x (pW x) (pD x) (pm0 x) (pK x) (pMmax x) E / Real.log (4 / 3)) _).trans
    (add_le_add h1 ?_)
  rw [abs_sub_comm]; exact h2

end P120


section P111
variable [hNS : Fact NumS]
include hNS
open Classical

/-- Tao Prop 1.11 in the draft's `Prop111` form (body inlined), from Prop 1.9 (`h19`), the box tail
(`hbox`), the deviation bounds, `proj_mu` and Prop 1.14 (`h114`, used at `A = 1`). -/
theorem prop111_of [hCb : Fact CbS]
    (h19 : ∀ (y : ℝ) (n : ℕ), 1 ≤ n → 2 * 2 ^ (3 * n) ≤ ⌈y⌉₊ → 0 < Z y →
      ∀ E : (Fin n → ℕ) → Prop,
      |prob y (fun N => E (vecn n N)) - ∑ v ∈ (Tset n).filter E, ((1 : ℝ) / 2) ^ absv v| ≤
        (2 * (2 ^ (6 * n + 1) / ((⌈y⌉₊ : ℝ) * Z y)) + 2) * (8 / 9) ^ n)
    (hbox : ∀ n : ℕ, 1 ≤ n →
      ∑ w ∈ (Box n (3 * n)).filter (fun w => 10 * (∑ i, w i) < 19 * n),
        ((1 : ℝ) / 2) ^ (∑ i, w i) ≤ Real.exp (-(n : ℝ) / 2400))
    (hdevK : ∀ (n K : ℕ) (C L : ℝ), 1 ≤ C → 0 ≤ L →
      ∑ w ∈ (Box n K).filter (fun w => ¬ DevOK C L (padv w) n),
        ((1 : ℝ) / 2) ^ (∑ i, w i) ≤ 2 * n * Real.exp (-(C * L) / 24))
    (hproj : ∀ (m j K : ℕ) (Z : ZMod (3 ^ m)), proj m (m + j) (mu (m + j) K) Z =
      mu m K Z * ∑ v ∈ Box j K, ((1 : ℝ) / 2) ^ (∑ i, v i))
    (h114 : ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧ ∀ m n K : ℕ, 1 ≤ m → m ≤ n → n ≤ K →
      Osc m n (mu n K) ≤ C * (m : ℝ) ^ (-A)) :
    ∃ C c x0 : ℝ, 0 < C ∧ 0 < c ∧ ∀ x : ℝ, x0 ≤ x →
      prob (x ^ alph) (fun N => ¬ Reaches x N) ≤ C * x ^ (-c) ∧
      prob (x ^ (alph ^ 2)) (fun N => ¬ Reaches x N) ≤ C * x ^ (-c) ∧
      ∀ E : ℕ → Prop,
        |prob (x ^ alph) (fun N => Reaches x N ∧ E (Pass x N)) -
          prob (x ^ (alph ^ 2)) (fun N => Reaches x N ∧ E (Pass x N))| ≤
          C * Real.log x ^ (-c) := by
  obtain ⟨C1, c1, x1, hC1, hc1, h1⟩ := p119 h19 hbox
  obtain ⟨Co, hCo, hosc⟩ := h114 1 one_pos
  obtain ⟨C2, x2, hC2, h2⟩ := p120 h19 (fun n C L hC hL => hdevK n (3 * n) C L hC hL) hdevK hproj
    ⟨Co, hCo.le, hosc⟩
  refine ⟨max C1 C2, min c1 (1 / 5), max (max x1 x2) (Real.exp 1), lt_max_of_lt_left hC1,
    lt_min hc1 (by norm_num), ?_⟩
  intro x hx
  have hx1 : x1 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hx2 : x2 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hxe : Real.exp 1 ≤ x := le_trans (le_max_right _ _) hx
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos 1) hxe
  have hxge1 : 1 ≤ x := le_trans (by linarith [Real.add_one_le_exp (1 : ℝ)]) hxe
  have hlx : 1 ≤ Real.log x := by rw [Real.le_log_iff_exp_le hx0]; exact hxe
  have hal : alph ≤ alph ^ 2 := by unfold alph; norm_num
  have hxa : x ≤ x ^ alph := by
    calc x = x ^ (1 : ℝ) := (Real.rpow_one x).symm
      _ ≤ x ^ alph := Real.rpow_le_rpow_of_exponent_le hxge1 (by unfold alph; norm_num)
  have hpow : x ^ (-c1) ≤ x ^ (-(min c1 (1 / 5))) :=
    Real.rpow_le_rpow_of_exponent_le hxge1 (by linarith [min_le_left c1 (1 / 5)])
  have hlog : Real.log x ^ (-((1 : ℝ) / 5)) ≤ Real.log x ^ (-(min c1 (1 / 5))) :=
    Real.rpow_le_rpow_of_exponent_le hlx (by linarith [min_le_right c1 (1 / 5)])
  have hxp : 0 ≤ x ^ (-c1) := Real.rpow_nonneg hx0.le _
  have hlp : 0 ≤ Real.log x ^ (-((1 : ℝ) / 5)) := Real.rpow_nonneg (by linarith) _
  have hb1 : C1 * x ^ (-c1) ≤ max C1 C2 * x ^ (-(min c1 (1 / 5))) :=
    mul_le_mul (le_max_left _ _) hpow hxp (le_trans hC1.le (le_max_left _ _))
  refine ⟨(h1 x hx1 _ hxa (Real.rpow_le_rpow_of_exponent_le hxge1 hal)).trans hb1,
    (h1 x hx1 _ (hxa.trans (Real.rpow_le_rpow_of_exponent_le hxge1 hal)) le_rfl).trans hb1, ?_⟩
  intro E
  exact (h2 x hx2 E).trans
    (mul_le_mul (le_max_right _ _) hlog hlp (le_trans hC1.le (le_max_left _ _)))

end P111
set_option autoImplicit false
set_option autoImplicit false
set_option autoImplicit false
lemma ps_succ (a : ℕ → ℕ) (j : ℕ) : ps a (j + 1) = ps a j + a j := rfl


section Four
open Finset
end Four
section Fact
open Finset
open Classical
lemma ps_eq_sum (a : ℕ → ℕ) (n : ℕ) : ps a n = ∑ j ∈ Finset.range n, a j := by
  induction n with
  | zero => rfl
  | succ n ih => rw [ps_succ, ih, Finset.sum_range_succ]


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
def Prop114 : Prop :=
  ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧ ∀ m n K : ℕ, 1 ≤ m → m ≤ n → n ≤ K →
    Osc m n (mu n K) ≤ C * (m : ℝ) ^ (-A)

/-- Def-free `mu` equation (child statement form). -/
def MuEq (n K : ℕ) (μ : ZMod (3 ^ n) → ℝ) : Prop :=
  ∀ Y : ZMod (3 ^ n), μ Y =
    ∑ w ∈ (Fintype.piFinset (fun _ : Fin n => Finset.Icc 1 K)).filter (fun w =>
      (((∑ j ∈ Finset.range n, 3 ^ j * 2 ^ ((∑ i ∈ Finset.range n,
              (if h : i < n then w ⟨i, h⟩ else 1)) -
            ∑ i ∈ Finset.range (j + 1), (if h : i < n then w ⟨i, h⟩ else 1)) : ℕ) : ZMod (3 ^ n)) *
          ((2 : ZMod (3 ^ n))⁻¹) ^ (∑ i ∈ Finset.range n, (if h : i < n then w ⟨i, h⟩ else 1))) = Y),
      ((1 : ℝ) / 2) ^ (∑ i, w i)

theorem mu_MuEq (n K : ℕ) : MuEq n K (mu n K) := by
  intro Y
  unfold mu Box syrZ Fnat padv
  simp only [ps_eq_sum]
  all_goals first
    | rfl
    | (congr 1; ext w; simp)
    | (simp only [Finset.filter_congr_decidable])
    | (convert rfl)

theorem Osc_eq_inl (m n : ℕ) (c : ZMod (3 ^ n) → ℝ) : Osc m n c =
    ∑ Y : ZMod (3 ^ n), |c Y - (3 : ℝ) ^ m / 3 ^ n *
      ∑ Y' ∈ Finset.univ.filter (fun Y' : ZMod (3 ^ n) => Y'.val % 3 ^ m = Y.val % 3 ^ m), c Y'| := by
  unfold Osc
  first
    | rfl
    | (simp only [Finset.filter_congr_decidable])
    | (convert rfl)

/-- Def-free Prop 1.14 (child statement body, `MuEq` unfolded in the spec). -/
def Prop114_inl : Prop :=
  ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧ ∀ m n K : ℕ, 1 ≤ m → m ≤ n → n ≤ K →
    ∀ μ : ZMod (3 ^ n) → ℝ, MuEq n K μ →
    ∑ Y : ZMod (3 ^ n), |μ Y - (3 : ℝ) ^ m / 3 ^ n *
      ∑ Y' ∈ Finset.univ.filter (fun Y' : ZMod (3 ^ n) => Y'.val % 3 ^ m = Y.val % 3 ^ m), μ Y'|
      ≤ C * (m : ℝ) ^ (-A)

theorem prop114_iff : Prop114 ↔ Prop114_inl := by
  constructor
  · intro h A hA
    obtain ⟨C, hC, hb⟩ := h A hA
    refine ⟨C, hC, fun m n K h1 h2 h3 μ hμ => ?_⟩
    have hμ' : μ = mu n K := funext fun Y => (hμ Y).trans (mu_MuEq n K Y).symm
    subst hμ'
    rw [← Osc_eq_inl]; exact hb m n K h1 h2 h3
  · intro h A hA
    obtain ⟨C, hC, hb⟩ := h A hA
    exact ⟨C, hC, fun m n K h1 h2 h3 => by
      rw [Osc_eq_inl]; exact hb m n K h1 h2 h3 _ (mu_MuEq n K)⟩

end IF114
section IF111
def Prop111 : Prop :=
  ∃ C c x0 : ℝ, 0 < C ∧ 0 < c ∧ ∀ x : ℝ, x0 ≤ x →
    prob (x ^ alph) (fun N => ¬ Reaches x N) ≤ C * x ^ (-c) ∧
    prob (x ^ (alph ^ 2)) (fun N => ¬ Reaches x N) ≤ C * x ^ (-c) ∧
    ∀ E : ℕ → Prop,
      |prob (x ^ alph) (fun N => Reaches x N ∧ E (Pass x N)) -
        prob (x ^ (alph ^ 2)) (fun N => Reaches x N ∧ E (Pass x N))| ≤ C * Real.log x ^ (-c)

/-- Def-free law of `N_y` (log-uniform odd integers in `[y, y^1.001]`). -/
def ProbEq (P : ℝ → (ℕ → Prop) → ℝ) : Prop :=
  ∀ (y : ℝ) (Q : ℕ → Prop), P y Q =
    (∑ N ∈ (Finset.Icc ⌈y⌉₊ ⌊y ^ ((1001 : ℝ) / 1000)⌋₊).filter Odd,
        Set.indicator {N | Q N} (fun N : ℕ => (1 : ℝ) / N) N) /
      ∑ N ∈ (Finset.Icc ⌈y⌉₊ ⌊y ^ ((1001 : ℝ) / 1000)⌋₊).filter Odd, (1 : ℝ) / N

theorem prob_ProbEq : ProbEq prob := by
  classical
  intro y Q
  unfold prob Z oddIcc alph
  simp only [Set.indicator_apply, Set.mem_ofPred_eq, Set.mem_setOf_eq]
  all_goals first
    | rfl
    | (simp only [Finset.filter_congr_decidable])
    | (convert rfl)

theorem pass_iff (x : ℝ) (N : ℕ) (E : ℕ → Prop) :
    (Reaches x N ∧ E (Pass x N)) ↔
      ∃ k, (syracuseStep^[k] N : ℝ) ≤ x ∧ (∀ j < k, x < (syracuseStep^[j] N : ℝ)) ∧
        E (syracuseStep^[k] N) := by
  classical
  constructor
  · rintro ⟨h, hE⟩
    have hT : T x N = Nat.find h := by unfold T; rw [dif_pos h]
    refine ⟨Nat.find h, Nat.find_spec h, fun j hj => lt_of_not_ge (Nat.find_min h hj), ?_⟩
    unfold Pass at hE; rw [hT] at hE; exact hE
  · rintro ⟨k, hk, hmin, hE⟩
    have h : Reaches x N := ⟨k, hk⟩
    have hfk : Nat.find h = k := by
      apply le_antisymm (Nat.find_min' h hk)
      by_contra hlt
      exact absurd (Nat.find_spec h) (not_le.2 (hmin _ (lt_of_not_ge hlt)))
    refine ⟨h, ?_⟩
    have hT : T x N = k := by unfold T; rw [dif_pos h]; exact hfk
    unfold Pass; rw [hT]; exact hE

/-- Def-free Prop 1.11 (child statement body, `ProbEq` unfolded in the spec). -/
def Prop111_inl : Prop :=
  ∀ P : ℝ → (ℕ → Prop) → ℝ, ProbEq P →
  ∃ C c x0 : ℝ, 0 < C ∧ 0 < c ∧ ∀ x : ℝ, x0 ≤ x →
    P (x ^ ((1001 : ℝ) / 1000)) (fun N => ¬ ∃ k, (syracuseStep^[k] N : ℝ) ≤ x) ≤ C * x ^ (-c) ∧
    P (x ^ (((1001 : ℝ) / 1000) ^ 2)) (fun N => ¬ ∃ k, (syracuseStep^[k] N : ℝ) ≤ x) ≤ C * x ^ (-c) ∧
    ∀ E : ℕ → Prop,
      |P (x ^ ((1001 : ℝ) / 1000)) (fun N => ∃ k, (syracuseStep^[k] N : ℝ) ≤ x ∧
          (∀ j < k, x < (syracuseStep^[j] N : ℝ)) ∧ E (syracuseStep^[k] N)) -
        P (x ^ (((1001 : ℝ) / 1000) ^ 2)) (fun N => ∃ k, (syracuseStep^[k] N : ℝ) ≤ x ∧
          (∀ j < k, x < (syracuseStep^[j] N : ℝ)) ∧ E (syracuseStep^[k] N))| ≤
        C * Real.log x ^ (-c)

theorem pass_fun (x : ℝ) (E : ℕ → Prop) :
    (fun N => Reaches x N ∧ E (Pass x N)) = (fun N => ∃ k, (syracuseStep^[k] N : ℝ) ≤ x ∧
      (∀ j < k, x < (syracuseStep^[j] N : ℝ)) ∧ E (syracuseStep^[k] N)) :=
  funext fun N => propext (pass_iff x N E)

theorem prop111_iff : Prop111 ↔ Prop111_inl := by
  constructor
  · rintro ⟨C, c, x0, hC, hc, hb⟩ P hP
    have hPp : P = prob := funext fun y => funext fun Q => (hP y Q).trans (prob_ProbEq y Q).symm
    subst hPp
    refine ⟨C, c, x0, hC, hc, fun x hx => ?_⟩
    obtain ⟨h1, h2, h3⟩ := hb x hx
    refine ⟨h1, h2, fun E => ?_⟩
    rw [← pass_fun]; exact h3 E
  · intro h
    obtain ⟨C, c, x0, hC, hc, hb⟩ := h prob prob_ProbEq
    refine ⟨C, c, x0, hC, hc, fun x hx => ?_⟩
    obtain ⟨h1, h2, h3⟩ := hb x hx
    refine ⟨h1, h2, fun E => ?_⟩
    have := h3 E
    rw [← pass_fun] at this
    exact this

end IF111
section C4
open Classical
end C4

section BridgeDefs
/-- Statement of the child `valuation_law_and_tails` (Prop 1.9 for `N_y`, tails, projection identity). -/
def C5S : Prop :=
  (∀ P : ℝ → (ℕ → Prop) → ℝ, (∀ (y : ℝ) (Q : ℕ → Prop), P y Q =
      (∑ N ∈ (Finset.Icc ⌈y⌉₊ ⌊y ^ ((1001 : ℝ) / 1000)⌋₊).filter Odd,
          Set.indicator {N | Q N} (fun N : ℕ => (1 : ℝ) / N) N) /
        ∑ N ∈ (Finset.Icc ⌈y⌉₊ ⌊y ^ ((1001 : ℝ) / 1000)⌋₊).filter Odd, (1 : ℝ) / N) →
      ∀ (y : ℝ) (n : ℕ), 1 ≤ n → 2 * 2 ^ (3 * n) ≤ ⌈y⌉₊ →
      0 < ∑ N ∈ (Finset.Icc ⌈y⌉₊ ⌊y ^ ((1001 : ℝ) / 1000)⌋₊).filter Odd, (1 : ℝ) / N →
      ∀ (E : (Fin n → ℕ) → Prop) [DecidablePred E],
      |P y (fun N => E (fun i => (3 * syracuseStep^[(i : ℕ)] N + 1).factorization 2)) -
        ∑ v ∈ ((Fintype.piFinset (fun _ : Fin n => Finset.Icc 1 (3 * n))).filter
            (fun v => ∑ i, v i < 3 * n)).filter E, ((1 : ℝ) / 2) ^ (∑ i, v i)| ≤
        (2 * (2 ^ (6 * n + 1) / ((⌈y⌉₊ : ℝ) *
          ∑ N ∈ (Finset.Icc ⌈y⌉₊ ⌊y ^ ((1001 : ℝ) / 1000)⌋₊).filter Odd, (1 : ℝ) / N)) + 2) *
          (8 / 9) ^ n) ∧
    (∀ (n K : ℕ), 1 ≤ n →
      ∑ w ∈ (Fintype.piFinset (fun _ : Fin n => Finset.Icc 1 K)).filter
          (fun w => 10 * (∑ i, w i) < 19 * n), ((1 : ℝ) / 2) ^ (∑ i, w i) ≤
        Real.exp (-(n : ℝ) / 2400)) ∧
    (∀ (n K : ℕ) (C L : ℝ), 1 ≤ C → 0 ≤ L →
      ∑ w ∈ Fintype.piFinset (fun _ : Fin n => Finset.Icc 1 K),
        Set.indicator {w : Fin n → ℕ | ∃ j ∈ Finset.Icc 1 n, C * (Real.sqrt (j * L) + L) <
            |((∑ i ∈ Finset.range j, (if h : i < n then w ⟨i, h⟩ else 1) : ℕ) : ℝ) - 2 * j|}
          (fun w => ((1 : ℝ) / 2) ^ (∑ i, w i)) w ≤ 2 * n * Real.exp (-(C * L) / 24)) ∧
    (∀ (m k K : ℕ) (μ₁ : ZMod (3 ^ m) → ℝ) (μ₂ : ZMod (3 ^ (m + k)) → ℝ),
      (∀ Y : ZMod (3 ^ m), μ₁ Y =
        ∑ w ∈ (Fintype.piFinset (fun _ : Fin m => Finset.Icc 1 K)).filter (fun w =>
          (((∑ j ∈ Finset.range m, 3 ^ j * 2 ^ ((∑ i ∈ Finset.range m,
                  (if h : i < m then w ⟨i, h⟩ else 1)) -
                ∑ i ∈ Finset.range (j + 1), (if h : i < m then w ⟨i, h⟩ else 1)) : ℕ) : ZMod (3 ^ m)) *
              ((2 : ZMod (3 ^ m))⁻¹) ^ (∑ i ∈ Finset.range m, (if h : i < m then w ⟨i, h⟩ else 1))) = Y),
          ((1 : ℝ) / 2) ^ (∑ i, w i)) →
      (∀ Y : ZMod (3 ^ (m + k)), μ₂ Y =
        ∑ w ∈ (Fintype.piFinset (fun _ : Fin (m + k) => Finset.Icc 1 K)).filter (fun w =>
          (((∑ j ∈ Finset.range (m + k), 3 ^ j * 2 ^ ((∑ i ∈ Finset.range (m + k),
                  (if h : i < m + k then w ⟨i, h⟩ else 1)) -
                ∑ i ∈ Finset.range (j + 1), (if h : i < m + k then w ⟨i, h⟩ else 1)) : ℕ) :
                  ZMod (3 ^ (m + k))) *
              ((2 : ZMod (3 ^ (m + k)))⁻¹) ^
                (∑ i ∈ Finset.range (m + k), (if h : i < m + k then w ⟨i, h⟩ else 1))) = Y),
          ((1 : ℝ) / 2) ^ (∑ i, w i)) →
      ∀ Z : ZMod (3 ^ m),
        ∑ Y ∈ Finset.univ.filter (fun Y : ZMod (3 ^ (m + k)) => ((Y.val : ℕ) : ZMod (3 ^ m)) = Z), μ₂ Y =
          μ₁ Z * ∑ v ∈ Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 K), ((1 : ℝ) / 2) ^ (∑ i, v i))

/-- Statement of the child `section5_parameter_estimates`. -/
def C6S : Prop :=
  ∀ (pn0 : ℝ → ℕ) (pD pL pW pWt peps : ℝ → ℝ) (pm0 pK pDm : ℝ → ℕ),
    (∀ x, pn0 x = ⌊Real.log x / (10 * Real.log 2)⌋₊) →
    (∀ x, pD x = 2 * Real.log x ^ ((3 : ℝ) / 5)) →
    (∀ x, pL x = Real.log x ^ ((1 : ℝ) / 5)) →
    (∀ x, pW x = 2 * ((2 * pD x + 1) * Real.log 2) + Real.log (4 / 3)) →
    (∀ x, pWt x = pW x + pD x * Real.log 2 + Real.log 2) →
    (∀ x, peps x = 2 * (3 / 2 : ℝ) ^ (pn0 x) / x) →
    (∀ x, pm0 x = ⌈(pW x + 2 * ((2 * pD x + 1) * Real.log 2) + 1) / Real.log (4 / 3)⌉₊) →
    (∀ x, pK x = ⌈2 * (pn0 x : ℝ) + pD x⌉₊) →
    (∀ x, pDm x = ⌈4 * pD x + 2⌉₊) →
    (∀ (x u : ℝ) (hu : 1000 ≤ u) (hx0 : 0 < x) (hx : Real.log x = u ^ 5),
      1 ≤ x ∧ 0 ≤ pD x ∧ pD x = 2 * u ^ 3 ∧ pL x = u ∧ 1000000 * u ^ 3 ≤ Real.log x ∧
    u ≤ u ^ 3 ∧ 6.931 * (pn0 x : ℝ) ≤ Real.log x ∧ Real.log x ≤ 6.932 * ((pn0 x : ℝ) + 1) ∧
    0 ≤ pW x ∧ pW x ≤ 6 * u ^ 3 ∧ 0 ≤ pWt x ∧ pWt x ≤ 8 * u ^ 3 ∧
    pW x + 2 * ((2 * pD x + 1) * Real.log 2) + 1 ≤ pm0 x * Real.log (4 / 3) ∧
    (pm0 x : ℝ) * Real.log (4 / 3) ≤ 13 * u ^ 3 ∧ (pm0 x : ℝ) ≤ 52 * u ^ 3 ∧ 1 ≤ pm0 x ∧
    u ≤ (pm0 x : ℝ) ∧ 2 * (pn0 x : ℝ) + pD x ≤ pK x ∧
    4 * pD x + 2 ≤ pDm x ∧ (pDm x : ℝ) ≤ 8 * u ^ 3 + 3) ∧
    (∀ (x u : ℝ) (hu : 1000 ≤ u) (hx0 : 0 < x) (hx : Real.log x = u ^ 5),
      0 ≤ peps x ∧ peps x * u ≤ 1 ∧ peps x ≤ 1 ∧ 2 * (3 / 2 : ℝ) ^ (pn0 x) ≤ peps x * x ∧
    4 * (3 : ℝ) ^ (pn0 x + pm0 x) * 2 ^ (pDm x) ≤ x ∧
    1 * (Real.sqrt (pn0 x * pL x) + pL x) ≤ pD x ∧ pm0 x ≤ pn0 x) ∧
    (∀ (x u a : ℝ) (hu : 1000 ≤ u) (hx0 : 0 < x) (hx : Real.log x = u ^ 5) (ha1 : 1001 / 1000 ≤ a) (ha2 : a ≤ 1002001 / 1000000),
      16 ≤ x ^ a ∧ x ≤ x ^ a ∧ x ^ a + 1 ≤ (x ^ a) ^ ((1001 : ℝ) / 1000) ∧ (4 : ℝ) ^ (pn0 x) ≤ x ^ a ∧
    ((1001 : ℝ) / 1000) * Real.log (x ^ a) + pn0 x * Real.log (3 / 4) + (2 * pD x + 1) * Real.log 2 ≤ Real.log x ∧
    (pm0 x + 1) * Real.log (4 / 3) + (2 * pD x + 1) * Real.log 2 ≤ Real.log (x ^ a) - Real.log x ∧
    2 * pm0 x * Real.log (4 / 3) ≤ Real.log (x ^ a) - Real.log x + pWt x ∧
    2 * pWt x ≤ Real.log (x ^ a) - Real.log x + pWt x ∧
    Real.log (x ^ a) - Real.log x + pWt x ≤ ((1001 : ℝ) / 1000) * Real.log (x ^ a) - Real.log x - pWt x ∧
    ((1001 : ℝ) / 1000) * Real.log (x ^ a) - Real.log x - pWt x ≤ pn0 x * Real.log (4 / 3) ∧
    4 ≤ (((1001 : ℝ) / 1000) - 1) * Real.log (x ^ a)) ∧
    (∀ (ε eb Wt Λ ly h u : ℝ) (hu : 1000 ≤ u) (hly : u ^ 5 / 1000 ≤ ly) (hε0 : 0 ≤ ε) (hεu : ε * u ≤ 1) (hε1 : ε ≤ 1) (heb : 0 ≤ eb) (hWt0 : 0 ≤ Wt) (hWt : Wt ≤ 8 * u ^ 3) (hΛ0 : 0 ≤ Λ) (hΛ : Λ ≤ 4) (ha : 1 / 4 ≤ h) (hb : h ≤ 1 / 3),
      (4 * (ε * (ly / h + 1) * 4 + (ly / h + 1) * eb + (1 + ε) * (2 * (2 * Wt / h + 1)) * 4) / ly +
      Λ * (4 * ((2 * Wt / h + 1) + 2 / h) / ly)) ≤ 5500 / u + 20 * eb) ∧
    (∀ (x u Cosc : ℝ) (hu : 1000 ≤ u) (hx0 : 0 < x) (hx : Real.log x = u ^ 5) (hCosc : 0 ≤ Cosc),
      4 * ((pn0 x : ℝ) * (1 / 2) ^ (pK x) + Cosc * (pm0 x : ℝ) ^ (-(1 : ℝ)) +
      2 * pn0 x * Real.exp (-(1 * pL x) / 24)) ≤ 4 * (1 + Cosc + 2 * 137594142720) / u) ∧
    (∀ (x u : ℝ) (hu : 1000 ≤ u) (hx0 : 0 < x) (hx : Real.log x = u ^ 5),
      8 * x ^ (-(1 / 20000 : ℝ)) + 2 * Real.log x * Real.exp (-(Real.log x ^ ((1 : ℝ) / 5)) / 24) ≤
      (8 + 2 * 137594142720) / u)

theorem Z_eqS (y : ℝ) :
    Z y = ∑ N ∈ (Finset.Icc ⌈y⌉₊ ⌊y ^ ((1001 : ℝ) / 1000)⌋₊).filter Odd, (1 : ℝ) / N := by
  unfold Z oddIcc alph
  first
    | rfl
    | (simp only [Finset.filter_congr_decidable])
    | (convert rfl)

theorem numS_of (h : C6S) : NumS :=
  h pn0 pD pL pW pWt peps pm0 pK pDm (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
end BridgeDefs

section Bridge5
open Classical

/-- Prop 1.11 from the child facts `C5S`, the numerics `NumS` and Prop 1.14. -/
theorem prop111_of5 (h5 : C5S) [Fact NumS] [Fact CbS] (h114 : Prop114) : Prop111 := by
  obtain ⟨h1, h2, h3, h4⟩ := h5
  refine prop111_of ?_ ?_ ?_ ?_ h114
  · intro y n hn hM hZ E
    rw [Z_eqS] at hZ ⊢
    exact h1 prob prob_ProbEq y n hn hM hZ E
  · intro n hn
    exact h2 n (3 * n) hn
  · intro n K C L hC hL
    have h := h3 n K C L hC hL
    rw [Finset.sum_filter]
    refine le_of_eq_of_le ?_ h
    apply Finset.sum_congr rfl
    intro w _
    by_cases hw : ∃ j ∈ Finset.Icc 1 n, C * (Real.sqrt (j * L) + L) <
        |((∑ i ∈ Finset.range j, (if h : i < n then w ⟨i, h⟩ else 1) : ℕ) : ℝ) - 2 * j|
    · simp only [Set.indicator_apply, Set.mem_ofPred_eq]
      rw [if_pos hw, if_pos]
      unfold DevOK padv
      simp only [ps_eq_sum, not_forall, not_le, exists_prop]
      exact hw
    · simp only [Set.indicator_apply, Set.mem_ofPred_eq]
      rw [if_neg hw, if_neg]
      intro hc
      apply hw
      unfold DevOK padv at hc
      simpa only [ps_eq_sum, not_forall, not_le, exists_prop] using hc
  · intro m j K Z
    exact h4 m j K (mu m K) (mu (m + j) K) (mu_MuEq m K) (mu_MuEq (m + j) K) Z
end Bridge5

end Tao31

open Tao31 in
theorem solution :
    (∀ (x : ℝ) (hx : 0 < x) (m k : ℕ) (hm : 1 ≤ m) (b : Fin m → ℕ) (S : Finset ℕ) (hsize : 4 * (3 : ℝ) ^ (k + m) * 2 ^ (b ⟨m - 1, by omega⟩) ≤ x) (hS : ∀ M ∈ S, (fun i : Fin m => (3 * syracuseStep^[(i : ℕ)] M + 1).factorization 2) = b ∧ (syracuseStep^[m] M : ℝ) ≤ x ∧ x < (syracuseStep^[m - 1] M : ℝ)) (hcong : ∀ M ∈ S, ∀ M' ∈ S, (3 : ℤ) ^ k ∣ (M' : ℤ) - M),
      (3 : ℝ) ^ k * ∑ M ∈ S, (1 : ℝ) / M ≤ ((1 : ℝ) / 2) ^ (∑ i, b i) * (2 + b ⟨m - 1, by omega⟩)) →
    ((∀ P : ℝ → (ℕ → Prop) → ℝ, (∀ (y : ℝ) (Q : ℕ → Prop), P y Q =
      (∑ N ∈ (Finset.Icc ⌈y⌉₊ ⌊y ^ ((1001 : ℝ) / 1000)⌋₊).filter Odd,
          Set.indicator {N | Q N} (fun N : ℕ => (1 : ℝ) / N) N) /
        ∑ N ∈ (Finset.Icc ⌈y⌉₊ ⌊y ^ ((1001 : ℝ) / 1000)⌋₊).filter Odd, (1 : ℝ) / N) →
      ∀ (y : ℝ) (n : ℕ), 1 ≤ n → 2 * 2 ^ (3 * n) ≤ ⌈y⌉₊ →
      0 < ∑ N ∈ (Finset.Icc ⌈y⌉₊ ⌊y ^ ((1001 : ℝ) / 1000)⌋₊).filter Odd, (1 : ℝ) / N →
      ∀ (E : (Fin n → ℕ) → Prop) [DecidablePred E],
      |P y (fun N => E (fun i => (3 * syracuseStep^[(i : ℕ)] N + 1).factorization 2)) -
        ∑ v ∈ ((Fintype.piFinset (fun _ : Fin n => Finset.Icc 1 (3 * n))).filter
            (fun v => ∑ i, v i < 3 * n)).filter E, ((1 : ℝ) / 2) ^ (∑ i, v i)| ≤
        (2 * (2 ^ (6 * n + 1) / ((⌈y⌉₊ : ℝ) *
          ∑ N ∈ (Finset.Icc ⌈y⌉₊ ⌊y ^ ((1001 : ℝ) / 1000)⌋₊).filter Odd, (1 : ℝ) / N)) + 2) *
          (8 / 9) ^ n) ∧
    (∀ (n K : ℕ), 1 ≤ n →
      ∑ w ∈ (Fintype.piFinset (fun _ : Fin n => Finset.Icc 1 K)).filter
          (fun w => 10 * (∑ i, w i) < 19 * n), ((1 : ℝ) / 2) ^ (∑ i, w i) ≤
        Real.exp (-(n : ℝ) / 2400)) ∧
    (∀ (n K : ℕ) (C L : ℝ), 1 ≤ C → 0 ≤ L →
      ∑ w ∈ Fintype.piFinset (fun _ : Fin n => Finset.Icc 1 K),
        Set.indicator {w : Fin n → ℕ | ∃ j ∈ Finset.Icc 1 n, C * (Real.sqrt (j * L) + L) <
            |((∑ i ∈ Finset.range j, (if h : i < n then w ⟨i, h⟩ else 1) : ℕ) : ℝ) - 2 * j|}
          (fun w => ((1 : ℝ) / 2) ^ (∑ i, w i)) w ≤ 2 * n * Real.exp (-(C * L) / 24)) ∧
    (∀ (m k K : ℕ) (μ₁ : ZMod (3 ^ m) → ℝ) (μ₂ : ZMod (3 ^ (m + k)) → ℝ),
      (∀ Y : ZMod (3 ^ m), μ₁ Y =
        ∑ w ∈ (Fintype.piFinset (fun _ : Fin m => Finset.Icc 1 K)).filter (fun w =>
          (((∑ j ∈ Finset.range m, 3 ^ j * 2 ^ ((∑ i ∈ Finset.range m,
                  (if h : i < m then w ⟨i, h⟩ else 1)) -
                ∑ i ∈ Finset.range (j + 1), (if h : i < m then w ⟨i, h⟩ else 1)) : ℕ) : ZMod (3 ^ m)) *
              ((2 : ZMod (3 ^ m))⁻¹) ^ (∑ i ∈ Finset.range m, (if h : i < m then w ⟨i, h⟩ else 1))) = Y),
          ((1 : ℝ) / 2) ^ (∑ i, w i)) →
      (∀ Y : ZMod (3 ^ (m + k)), μ₂ Y =
        ∑ w ∈ (Fintype.piFinset (fun _ : Fin (m + k) => Finset.Icc 1 K)).filter (fun w =>
          (((∑ j ∈ Finset.range (m + k), 3 ^ j * 2 ^ ((∑ i ∈ Finset.range (m + k),
                  (if h : i < m + k then w ⟨i, h⟩ else 1)) -
                ∑ i ∈ Finset.range (j + 1), (if h : i < m + k then w ⟨i, h⟩ else 1)) : ℕ) :
                  ZMod (3 ^ (m + k))) *
              ((2 : ZMod (3 ^ (m + k)))⁻¹) ^
                (∑ i ∈ Finset.range (m + k), (if h : i < m + k then w ⟨i, h⟩ else 1))) = Y),
          ((1 : ℝ) / 2) ^ (∑ i, w i)) →
      ∀ Z : ZMod (3 ^ m),
        ∑ Y ∈ Finset.univ.filter (fun Y : ZMod (3 ^ (m + k)) => ((Y.val : ℕ) : ZMod (3 ^ m)) = Z), μ₂ Y =
          μ₁ Z * ∑ v ∈ Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 K), ((1 : ℝ) / 2) ^ (∑ i, v i))) →
    (∀ (pn0 : ℝ → ℕ) (pD pL pW pWt peps : ℝ → ℝ) (pm0 pK pDm : ℝ → ℕ),
    (∀ x, pn0 x = ⌊Real.log x / (10 * Real.log 2)⌋₊) →
    (∀ x, pD x = 2 * Real.log x ^ ((3 : ℝ) / 5)) →
    (∀ x, pL x = Real.log x ^ ((1 : ℝ) / 5)) →
    (∀ x, pW x = 2 * ((2 * pD x + 1) * Real.log 2) + Real.log (4 / 3)) →
    (∀ x, pWt x = pW x + pD x * Real.log 2 + Real.log 2) →
    (∀ x, peps x = 2 * (3 / 2 : ℝ) ^ (pn0 x) / x) →
    (∀ x, pm0 x = ⌈(pW x + 2 * ((2 * pD x + 1) * Real.log 2) + 1) / Real.log (4 / 3)⌉₊) →
    (∀ x, pK x = ⌈2 * (pn0 x : ℝ) + pD x⌉₊) →
    (∀ x, pDm x = ⌈4 * pD x + 2⌉₊) →
    (∀ (x u : ℝ) (hu : 1000 ≤ u) (hx0 : 0 < x) (hx : Real.log x = u ^ 5),
      1 ≤ x ∧ 0 ≤ pD x ∧ pD x = 2 * u ^ 3 ∧ pL x = u ∧ 1000000 * u ^ 3 ≤ Real.log x ∧
    u ≤ u ^ 3 ∧ 6.931 * (pn0 x : ℝ) ≤ Real.log x ∧ Real.log x ≤ 6.932 * ((pn0 x : ℝ) + 1) ∧
    0 ≤ pW x ∧ pW x ≤ 6 * u ^ 3 ∧ 0 ≤ pWt x ∧ pWt x ≤ 8 * u ^ 3 ∧
    pW x + 2 * ((2 * pD x + 1) * Real.log 2) + 1 ≤ pm0 x * Real.log (4 / 3) ∧
    (pm0 x : ℝ) * Real.log (4 / 3) ≤ 13 * u ^ 3 ∧ (pm0 x : ℝ) ≤ 52 * u ^ 3 ∧ 1 ≤ pm0 x ∧
    u ≤ (pm0 x : ℝ) ∧ 2 * (pn0 x : ℝ) + pD x ≤ pK x ∧
    4 * pD x + 2 ≤ pDm x ∧ (pDm x : ℝ) ≤ 8 * u ^ 3 + 3) ∧
    (∀ (x u : ℝ) (hu : 1000 ≤ u) (hx0 : 0 < x) (hx : Real.log x = u ^ 5),
      0 ≤ peps x ∧ peps x * u ≤ 1 ∧ peps x ≤ 1 ∧ 2 * (3 / 2 : ℝ) ^ (pn0 x) ≤ peps x * x ∧
    4 * (3 : ℝ) ^ (pn0 x + pm0 x) * 2 ^ (pDm x) ≤ x ∧
    1 * (Real.sqrt (pn0 x * pL x) + pL x) ≤ pD x ∧ pm0 x ≤ pn0 x) ∧
    (∀ (x u a : ℝ) (hu : 1000 ≤ u) (hx0 : 0 < x) (hx : Real.log x = u ^ 5) (ha1 : 1001 / 1000 ≤ a) (ha2 : a ≤ 1002001 / 1000000),
      16 ≤ x ^ a ∧ x ≤ x ^ a ∧ x ^ a + 1 ≤ (x ^ a) ^ ((1001 : ℝ) / 1000) ∧ (4 : ℝ) ^ (pn0 x) ≤ x ^ a ∧
    ((1001 : ℝ) / 1000) * Real.log (x ^ a) + pn0 x * Real.log (3 / 4) + (2 * pD x + 1) * Real.log 2 ≤ Real.log x ∧
    (pm0 x + 1) * Real.log (4 / 3) + (2 * pD x + 1) * Real.log 2 ≤ Real.log (x ^ a) - Real.log x ∧
    2 * pm0 x * Real.log (4 / 3) ≤ Real.log (x ^ a) - Real.log x + pWt x ∧
    2 * pWt x ≤ Real.log (x ^ a) - Real.log x + pWt x ∧
    Real.log (x ^ a) - Real.log x + pWt x ≤ ((1001 : ℝ) / 1000) * Real.log (x ^ a) - Real.log x - pWt x ∧
    ((1001 : ℝ) / 1000) * Real.log (x ^ a) - Real.log x - pWt x ≤ pn0 x * Real.log (4 / 3) ∧
    4 ≤ (((1001 : ℝ) / 1000) - 1) * Real.log (x ^ a)) ∧
    (∀ (ε eb Wt Λ ly h u : ℝ) (hu : 1000 ≤ u) (hly : u ^ 5 / 1000 ≤ ly) (hε0 : 0 ≤ ε) (hεu : ε * u ≤ 1) (hε1 : ε ≤ 1) (heb : 0 ≤ eb) (hWt0 : 0 ≤ Wt) (hWt : Wt ≤ 8 * u ^ 3) (hΛ0 : 0 ≤ Λ) (hΛ : Λ ≤ 4) (ha : 1 / 4 ≤ h) (hb : h ≤ 1 / 3),
      (4 * (ε * (ly / h + 1) * 4 + (ly / h + 1) * eb + (1 + ε) * (2 * (2 * Wt / h + 1)) * 4) / ly +
      Λ * (4 * ((2 * Wt / h + 1) + 2 / h) / ly)) ≤ 5500 / u + 20 * eb) ∧
    (∀ (x u Cosc : ℝ) (hu : 1000 ≤ u) (hx0 : 0 < x) (hx : Real.log x = u ^ 5) (hCosc : 0 ≤ Cosc),
      4 * ((pn0 x : ℝ) * (1 / 2) ^ (pK x) + Cosc * (pm0 x : ℝ) ^ (-(1 : ℝ)) +
      2 * pn0 x * Real.exp (-(1 * pL x) / 24)) ≤ 4 * (1 + Cosc + 2 * 137594142720) / u) ∧
    (∀ (x u : ℝ) (hu : 1000 ≤ u) (hx0 : 0 < x) (hx : Real.log x = u ^ 5),
      8 * x ^ (-(1 / 20000 : ℝ)) + 2 * Real.log x * Real.exp (-(Real.log x ^ ((1 : ℝ) / 5)) / 24) ≤
      (8 + 2 * 137594142720) / u)) →
    (∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧ ∀ m n K : ℕ, 1 ≤ m → m ≤ n → n ≤ K →
    ∀ μ : ZMod (3 ^ n) → ℝ, (∀ Y : ZMod (3 ^ n), μ Y =
    ∑ w ∈ (Fintype.piFinset (fun _ : Fin n => Finset.Icc 1 K)).filter (fun w =>
      (((∑ j ∈ Finset.range n, 3 ^ j * 2 ^ ((∑ i ∈ Finset.range n,
              (if h : i < n then w ⟨i, h⟩ else 1)) -
            ∑ i ∈ Finset.range (j + 1), (if h : i < n then w ⟨i, h⟩ else 1)) : ℕ) : ZMod (3 ^ n)) *
          ((2 : ZMod (3 ^ n))⁻¹) ^ (∑ i ∈ Finset.range n, (if h : i < n then w ⟨i, h⟩ else 1))) = Y),
      ((1 : ℝ) / 2) ^ (∑ i, w i)) →
    ∑ Y : ZMod (3 ^ n), |μ Y - (3 : ℝ) ^ m / 3 ^ n *
      ∑ Y' ∈ Finset.univ.filter (fun Y' : ZMod (3 ^ n) => Y'.val % 3 ^ m = Y.val % 3 ^ m), μ Y'|
      ≤ C * (m : ℝ) ^ (-A)) →
  ∀ P : ℝ → (ℕ → Prop) → ℝ, (∀ (y : ℝ) (Q : ℕ → Prop), P y Q =
    (∑ N ∈ (Finset.Icc ⌈y⌉₊ ⌊y ^ ((1001 : ℝ) / 1000)⌋₊).filter Odd,
        Set.indicator {N | Q N} (fun N : ℕ => (1 : ℝ) / N) N) /
      ∑ N ∈ (Finset.Icc ⌈y⌉₊ ⌊y ^ ((1001 : ℝ) / 1000)⌋₊).filter Odd, (1 : ℝ) / N) →
  ∃ C c x0 : ℝ, 0 < C ∧ 0 < c ∧ ∀ x : ℝ, x0 ≤ x →
    P (x ^ ((1001 : ℝ) / 1000)) (fun N => ¬ ∃ k, (syracuseStep^[k] N : ℝ) ≤ x) ≤ C * x ^ (-c) ∧
    P (x ^ (((1001 : ℝ) / 1000) ^ 2)) (fun N => ¬ ∃ k, (syracuseStep^[k] N : ℝ) ≤ x) ≤ C * x ^ (-c) ∧
    ∀ E : ℕ → Prop,
      |P (x ^ ((1001 : ℝ) / 1000)) (fun N => ∃ k, (syracuseStep^[k] N : ℝ) ≤ x ∧
          (∀ j < k, x < (syracuseStep^[j] N : ℝ)) ∧ E (syracuseStep^[k] N)) -
        P (x ^ (((1001 : ℝ) / 1000) ^ 2)) (fun N => ∃ k, (syracuseStep^[k] N : ℝ) ≤ x ∧
          (∀ j < k, x < (syracuseStep^[j] N : ℝ)) ∧ E (syracuseStep^[k] N))| ≤
        C * Real.log x ^ (-c) := by
  intro h7 h5 h6 h
  haveI : Fact Tao31.CbS := ⟨h7⟩
  haveI : Fact Tao31.NumS := ⟨Tao31.numS_of h6⟩
  exact Tao31.prop111_iff.1 (Tao31.prop111_of5 h5 (Tao31.prop114_iff.2 h))
