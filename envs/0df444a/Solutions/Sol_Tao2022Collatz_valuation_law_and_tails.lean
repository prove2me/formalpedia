-- Prove2me | solution 1 for Tao2022Collatz.valuation_law_and_tails
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-12T01:34:25.68707+00:00
-- url     : https://prove2.me/submissions/28f17d2d-ceff-4a30-8065-dd9e0b91f1a8

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
section Item6a3
end Item6a3
def ps (a : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | j + 1 => ps a j + a j

def padv {n : ℕ} (w : Fin n → ℕ) : ℕ → ℕ := fun i => if h : i < n then w ⟨i, h⟩ else 1

def DevOK (C L : ℝ) (a : ℕ → ℕ) (k : ℕ) : Prop :=
  ∀ j ∈ Finset.Icc 1 k, |(ps a j : ℝ) - 2 * j| ≤ C * (Real.sqrt (j * L) + L)

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
end Item6d
section Item6d2
end Item6d2
section Item6d3
open Classical
end Item6d3
section ZAsymp
end ZAsymp
section Item6e1
open Classical
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
def Fnat (a : ℕ → ℕ) (n : ℕ) : ℕ := ∑ j ∈ Finset.range n, 3 ^ j * 2 ^ (ps a n - ps a (j + 1))

noncomputable def syrZ (n : ℕ) (a : ℕ → ℕ) : ZMod (3 ^ n) :=
  (Fnat a n : ZMod (3 ^ n)) * ((2 : ZMod (3 ^ n))⁻¹) ^ ps a n

lemma two_mul_inv (n : ℕ) : (2 : ZMod (3 ^ n)) * (2 : ZMod (3 ^ n))⁻¹ = 1 := by
  have hc : Nat.Coprime 2 (3 ^ n) := Nat.Coprime.pow_right _ (by norm_num)
  have := ZMod.coe_mul_inv_eq_one (n := 3 ^ n) 2 hc
  simpa using this



section Item6e5
open Classical
lemma Av_ge (v : ℕ → ℕ) (hv : ∀ i, 1 ≤ v i) : ∀ k, k ≤ Av v k
  | 0 => by simp [Av]
  | k + 1 => by have := Av_ge v hv k; have := hv k; simp only [Av]; omega

lemma Sv_odd (v : ℕ → ℕ) (hv : ∀ i, 1 ≤ v i) : ∀ k, 1 ≤ k → Odd (Sv v k)
  | 0, h => absurd h (by norm_num)
  | 1, _ => by simp [Sv, Av]
  | k + 2, _ => by
    have ih := Sv_odd v hv (k + 1) (by omega)
    have hA : 1 ≤ Av v (k + 1) := le_trans (by omega) (Av_ge v hv (k + 1))
    rw [Sv]
    have he : Even (2 ^ Av v (k + 1)) := Nat.even_pow.2 ⟨even_two, by omega⟩
    exact (Odd.mul ⟨1, by norm_num⟩ ih).add_even he

noncomputable def mu (n K : ℕ) (Y : ZMod (3 ^ n)) : ℝ :=
  ∑ w ∈ (Box n K).filter (fun w => syrZ n (padv w) = Y), ((1 : ℝ) / 2) ^ (∑ i, w i)

noncomputable def Osc (m n : ℕ) (c : ZMod (3 ^ n) → ℝ) : ℝ :=
  ∑ Y : ZMod (3 ^ n), |c Y - (3 : ℝ) ^ m / 3 ^ n *
    ∑ Y' ∈ Finset.univ.filter (fun Y' : ZMod (3 ^ n) => Y'.val % 3 ^ m = Y.val % 3 ^ m), c Y'|

def red (m n : ℕ) (Y : ZMod (3 ^ n)) : ZMod (3 ^ m) := (Y.val : ZMod (3 ^ m))

noncomputable def proj (m n : ℕ) (c : ZMod (3 ^ n) → ℝ) (Z : ZMod (3 ^ m)) : ℝ :=
  ∑ Y ∈ Finset.univ.filter (fun Y => red m n Y = Z), c Y

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
/-- Odd inputs give odd outputs (the step removes all factors of 2). -/
lemma step_odd (n : ℕ) : Odd (syracuseStep n) := by
  unfold syracuseStep
  have hpos : 3 * n + 1 ≠ 0 := by omega
  have := Nat.coprime_ordCompl Nat.prime_two hpos
  rw [Nat.odd_iff]
  have h2 : ¬ 2 ∣ ordCompl[2] (3 * n + 1) := Nat.not_dvd_ordCompl Nat.prime_two hpos
  omega


/-! DECOMPOSE item 2: trivial mass bound and reduction to large thresholds. -/
lemma iterate_odd (N : ℕ) (hN : Odd N) (k : ℕ) : Odd (syracuseStep^[k] N) := by
  cases k with
  | zero => simpa using hN
  | succ k => rw [Function.iterate_succ_apply']; exact step_odd _


/-- Forward direction of Lemma 2.1. -/
lemma valuation_char_mp (N : ℕ) (hN : Odd N) (v : ℕ → ℕ) (k : ℕ)
    (h : ∀ i < k, a (syracuseStep^[i] N) = v i) :
    ∃ m, Odd m ∧ 2 ^ Av v k * m = 3 ^ k * N + Sv v k := by
  obtain ⟨h1, h2⟩ := AvSv_congr (fun i => a (syracuseStep^[i] N)) v k h
  obtain ⟨h3, h4⟩ := A_S_eq N k
  refine ⟨syracuseStep^[k] N, iterate_odd N hN k, ?_⟩
  rw [← h1, ← h2, ← h3, ← h4]
  exact iterate_formula N k


/-- Tao Lemma 2.1 (arithmetic form). -/
theorem valuation_char (N : ℕ) (hN : Odd N) (v : ℕ → ℕ) (hv : ∀ i, 1 ≤ v i) (k : ℕ) :
    (∀ i < k, a (syracuseStep^[i] N) = v i) ↔
      ∃ m, Odd m ∧ 2 ^ Av v k * m = 3 ^ k * N + Sv v k :=
  ⟨valuation_char_mp N hN v k, valuation_char_mpr N hN v hv k⟩


/-! DECOMPOSE item 5 setup: log-uniform odd variables `N_y`, first passage, Prop 1.11 interface. -/
/-! DECOMPOSE item 4 (Tao Section 4, Prop 1.9 with `n' = 3n`): arithmetic/counting layer. -/
lemma exists_odd_iff_mod (s X : ℕ) : (∃ m, Odd m ∧ 2 ^ s * m = X) ↔ X % 2 ^ (s + 1) = 2 ^ s := by
  constructor
  · rintro ⟨m, ⟨j, rfl⟩, rfl⟩
    have h : 2 ^ s * (2 * j + 1) = 2 ^ s + 2 ^ (s + 1) * j := by ring
    have hlt : 2 ^ s < 2 ^ (s + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    rw [h, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
  · intro h
    have hX := Nat.div_add_mod X (2 ^ (s + 1))
    rw [h] at hX
    refine ⟨2 * (X / 2 ^ (s + 1)) + 1, ⟨_, rfl⟩, ?_⟩
    calc 2 ^ s * (2 * (X / 2 ^ (s + 1)) + 1) = 2 ^ (s + 1) * (X / 2 ^ (s + 1)) + 2 ^ s := by ring
      _ = X := hX


/-- Lemma 2.1 in residue form for tuples. -/
lemma vecn_eq_iff (n N : ℕ) (hN : Odd N) (w : Fin n → ℕ) (hw : ∀ i, 1 ≤ w i) :
    vecn n N = w ↔ (3 ^ n * N + Sv (padv w) n) % 2 ^ (absv w + 1) = 2 ^ absv w := by
  have hp : ∀ i, 1 ≤ padv w i := by
    intro i; unfold padv; split_ifs <;> simp [hw]
  rw [← Av_padv w, ← exists_odd_iff_mod, ← valuation_char N hN (padv w) hp n]
  constructor
  · rintro rfl i hi
    simp [padv, hi, vecn]
  · intro h
    funext i
    have := h i i.isLt
    show a (syracuseStep^[(i : ℕ)] N) = w i
    rw [this]; simp [padv]


lemma Tset_pos {n : ℕ} {w : Fin n → ℕ} (hT : w ∈ Tset n) (i : Fin n) : 1 ≤ w i := by
  have := (Finset.mem_filter.1 hT).1
  rw [Bset, Fintype.mem_piFinset] at this
  exact (Finset.mem_Icc.1 (this i)).1


lemma Tset_abs {n : ℕ} {w : Fin n → ℕ} (hT : w ∈ Tset n) : absv w + 1 ≤ 3 * n := by
  have := (Finset.mem_filter.1 hT).2; omega


lemma mod_transfer (n N N' S s : ℕ) (hs : s + 1 ≤ 3 * n) (h : N % 2 ^ (3 * n) = N' % 2 ^ (3 * n)) :
    (3 ^ n * N + S) % 2 ^ (s + 1) = (3 ^ n * N' + S) % 2 ^ (s + 1) := by
  have h1 : N ≡ N' [MOD 2 ^ (s + 1)] := Nat.ModEq.of_dvd (pow_dvd_pow 2 hs) h
  exact (h1.mul_left _).add_right _


/-- For `|a⃗| < 3n` the event `a⃗^{(n)}(N) = a⃗` depends only on `N mod 2^{3n}`. -/
lemma vecn_transfer (n N N' : ℕ) (hN : Odd N) (hN' : Odd N') (h : N % 2 ^ (3 * n) = N' % 2 ^ (3 * n))
    (hT : vecn n N ∈ Tset n) : vecn n N' = vecn n N := by
  have hw := Tset_pos hT
  rw [vecn_eq_iff n N' hN' _ hw, ← mod_transfer n N N' _ _ (Tset_abs hT) h]
  exact (vecn_eq_iff n N hN _ hw).1 rfl


lemma card_filter_range_periodic (P : ℕ → Prop) [DecidablePred P] (M q : ℕ)
    (hP : ∀ r, P (r % M) ↔ P r) :
    ((Finset.range (M * q)).filter P).card = q * ((Finset.range M).filter P).card := by
  rw [← Nat.count_eq_card_filter_range, ← Nat.count_eq_card_filter_range]
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Nat.mul_succ, Nat.count_add, ih]
    have hk : ∀ k, P (M * q + k) ↔ P k := by
      intro k
      have : (M * q + k) % M = k % M := by
        rw [Nat.add_mod, Nat.mul_mod_right, zero_add, Nat.mod_mod]
      rw [← hP (M * q + k), ← hP k, this]
    simp only [Nat.count_eq_card_filter_range]
    rw [Finset.filter_congr (fun k _ => hk k)]
    ring


lemma card_affine_mod (c S t M : ℕ) (hM : 0 < M) (hc : Nat.Coprime c M) (ht : t < M) :
    ((Finset.range M).filter (fun r => (c * r + S) % M = t)).card = 1 := by
  have hinj : Set.InjOn (fun r => (c * r + S) % M) (Finset.range M : Set ℕ) := by
    intro r hr r' hr' h
    simp only [Finset.coe_range, Set.mem_Iio] at hr hr'
    have h1 : c * r + S ≡ c * r' + S [MOD M] := h
    have h2 : c * r ≡ c * r' [MOD M] := Nat.ModEq.add_right_cancel' S h1
    have h3 : r ≡ r' [MOD M] := Nat.ModEq.cancel_left_of_coprime hc.symm h2
    unfold Nat.ModEq at h3
    rwa [Nat.mod_eq_of_lt hr, Nat.mod_eq_of_lt hr'] at h3
  have himg : (Finset.range M).image (fun r => (c * r + S) % M) = Finset.range M := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      simp only [Finset.mem_image, Finset.mem_range] at hx ⊢
      obtain ⟨r, _, rfl⟩ := hx
      exact Nat.mod_lt _ hM
    · rw [Finset.card_image_of_injOn hinj]
  have hmem : t ∈ (Finset.range M).image (fun r => (c * r + S) % M) := by
    rw [himg]; exact Finset.mem_range.2 ht
  obtain ⟨r0, hr0, hr0t⟩ := Finset.mem_image.1 hmem
  rw [Finset.card_eq_one]
  refine ⟨r0, ?_⟩
  ext r
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
  constructor
  · rintro ⟨hr, hrt⟩
    exact hinj (Finset.mem_coe.2 (Finset.mem_range.2 hr)) (Finset.mem_coe.2 hr0)
      (hrt.trans hr0t.symm)
  · rintro rfl
    exact ⟨Finset.mem_range.1 hr0, hr0t⟩


/-- Odd residues mod `2^{3n}` (the uniform reference variable). -/
noncomputable def Rset (n : ℕ) : Finset ℕ := (Finset.range (2 ^ (3 * n))).filter Odd


lemma card_Rset (n : ℕ) (hn : 1 ≤ n) : (Rset n).card = 2 ^ (3 * n - 1) := by
  have h2 : 2 ^ (3 * n) = 2 * 2 ^ (3 * n - 1) := by rw [← pow_succ']; congr 1; omega
  rw [Rset, h2, card_filter_range_periodic Odd 2 _ (fun r => by simp [Nat.odd_iff])]
  have : ((Finset.range 2).filter Odd).card = 1 := by decide
  rw [this, mul_one]


/-- Exact count (Tao §4): `#{r odd < 2^{3n} : a⃗^{(n)}(r) = a⃗} = 2^{3n-|a⃗|-1}` for `|a⃗| < 3n`. -/
lemma card_vecn_eq (n : ℕ) (w : Fin n → ℕ) (hT : w ∈ Tset n) :
    ((Rset n).filter (fun r => vecn n r = w)).card = 2 ^ (3 * n - (absv w + 1)) := by
  have hw := Tset_pos hT
  have hs3 := Tset_abs hT
  set s := absv w with hsdef
  set S := Sv (padv w) n with hSdef
  have hp : ∀ i, 1 ≤ padv w i := by
    intro i; unfold padv; split_ifs <;> simp [hw]
  have hsn : n ≤ s := by rw [hsdef, ← Av_padv]; exact Av_ge _ hp n
  have hn : 1 ≤ n := by omega
  have hSodd : Odd S := Sv_odd _ hp n hn
  have hodd : ∀ r, (3 ^ n * r + S) % 2 ^ (s + 1) = 2 ^ s → Odd r := by
    intro r hr
    by_contra hre
    rw [Nat.not_odd_iff_even] at hre
    have hX : Odd (3 ^ n * r + S) := (hre.mul_left _).add_odd hSodd
    have h2 : (3 ^ n * r + S) % 2 ^ (s + 1) % 2 = (3 ^ n * r + S) % 2 :=
      Nat.mod_mod_of_dvd _ (dvd_pow_self 2 (by omega))
    rw [hr, Nat.odd_iff.1 hX] at h2
    have : 2 ^ s % 2 = 0 := Nat.mod_eq_zero_of_dvd (dvd_pow_self 2 (by omega))
    omega
  have hfilt : (Rset n).filter (fun r => vecn n r = w) =
      (Finset.range (2 ^ (3 * n))).filter (fun r => (3 ^ n * r + S) % 2 ^ (s + 1) = 2 ^ s) := by
    ext r
    simp only [Rset, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨⟨hr, ho⟩, hv⟩
      exact ⟨hr, (vecn_eq_iff n r ho w hw).1 hv⟩
    · rintro ⟨hr, hc⟩
      have ho := hodd r hc
      exact ⟨⟨hr, ho⟩, (vecn_eq_iff n r ho w hw).2 hc⟩
  have hpow : 2 ^ (3 * n) = 2 ^ (s + 1) * 2 ^ (3 * n - (s + 1)) := by
    rw [← pow_add]; congr 1; omega
  rw [hfilt, hpow, card_filter_range_periodic _ (2 ^ (s + 1)) _ (fun r => by
      rw [((Nat.mod_modEq r (2 ^ (s + 1))).mul_left (3 ^ n)).add_right S]),
    card_affine_mod (3 ^ n) S (2 ^ s) (2 ^ (s + 1)) (by positivity)
      (Nat.Coprime.pow _ _ (by norm_num)) (Nat.pow_lt_pow_right (by norm_num) (by omega)), mul_one]


/-! Geometric weights `P(Geom(2)^n = a⃗) = 2^{-|a⃗|}` on `Tset n` (Tao Lemma 2.2 tail, finite form). -/
lemma geom_sum_half (L : ℕ) : ∑ j ∈ Finset.Icc 1 L, ((1 : ℝ) / 2) ^ j = 1 - (1 / 2) ^ L := by
  induction L with
  | zero => simp
  | succ L ih => rw [Finset.sum_Icc_succ_top (by omega), ih]; ring


lemma geom_sum_34 (L : ℕ) : ∑ j ∈ Finset.Icc 1 L, ((3 : ℝ) / 4) ^ j = 3 * (1 - (3 / 4) ^ L) := by
  induction L with
  | zero => simp
  | succ L ih => rw [Finset.sum_Icc_succ_top (by omega), ih]; ring


lemma sum_pi_pow (n L : ℕ) (x : ℝ) :
    ∑ v ∈ Fintype.piFinset (fun _ : Fin n => Finset.Icc 1 L), x ^ absv v =
      (∑ j ∈ Finset.Icc 1 L, x ^ j) ^ n := by
  rw [← Fin.prod_const, Finset.prod_univ_sum]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  rw [absv, Finset.prod_pow_eq_pow_sum]


lemma geomT_bounds (n : ℕ) :
    1 - (n : ℝ) * (1 / 2) ^ (3 * n) - (8 / 9) ^ n ≤ ∑ v ∈ Tset n, ((1 : ℝ) / 2) ^ absv v ∧
      ∑ v ∈ Tset n, ((1 : ℝ) / 2) ^ absv v ≤ 1 := by
  set y : ℝ := (1 / 2) ^ (3 * n) with hy
  have hy0 : 0 ≤ y := by positivity
  have hy1 : y ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hB : ∑ v ∈ Bset n, ((1 : ℝ) / 2) ^ absv v = (1 - y) ^ n := by
    rw [Bset, sum_pi_pow, geom_sum_half]
  have hsplit := Finset.sum_filter_add_sum_filter_not (Bset n) (fun v => absv v < 3 * n)
    (fun v => ((1 : ℝ) / 2) ^ absv v)
  have htail : ∑ v ∈ (Bset n).filter (fun v => ¬ absv v < 3 * n), ((1 : ℝ) / 2) ^ absv v
      ≤ (8 / 9) ^ n := by
    calc _ ≤ ∑ v ∈ (Bset n).filter (fun v => ¬ absv v < 3 * n),
          ((1 : ℝ) / 2) ^ absv v * ((3 / 2) ^ absv v / (3 / 2) ^ (3 * n)) := by
            apply Finset.sum_le_sum
            intro v hv
            have h := (Finset.mem_filter.1 hv).2
            have h1 : (1 : ℝ) ≤ (3 / 2) ^ absv v / (3 / 2) ^ (3 * n) := by
              rw [le_div_iff₀ (by positivity), one_mul]
              exact pow_le_pow_right₀ (by norm_num) (by omega)
            have h0 : (0 : ℝ) ≤ (1 / 2) ^ absv v := by positivity
            nlinarith
      _ ≤ ∑ v ∈ Bset n, ((1 : ℝ) / 2) ^ absv v * ((3 / 2) ^ absv v / (3 / 2) ^ (3 * n)) :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
              (fun _ _ _ => by positivity)
      _ = (∑ v ∈ Bset n, ((3 : ℝ) / 4) ^ absv v) / (3 / 2) ^ (3 * n) := by
            rw [Finset.sum_div]
            refine Finset.sum_congr rfl (fun v _ => ?_)
            rw [← mul_div_assoc, ← mul_pow]; norm_num
      _ = (3 * (1 - (3 / 4) ^ (3 * n))) ^ n / (3 / 2) ^ (3 * n) := by
            rw [Bset, sum_pi_pow, geom_sum_34]
      _ ≤ 3 ^ n / (3 / 2) ^ (3 * n) := by
            have hz0 : (0 : ℝ) ≤ (3 / 4) ^ (3 * n) := by positivity
            have hz1 : ((3 : ℝ) / 4) ^ (3 * n) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
            gcongr
            all_goals nlinarith
      _ = (8 / 9) ^ n := by rw [pow_mul, ← div_pow]; norm_num
  have hbern : 1 - (n : ℝ) * y ≤ (1 - y) ^ n := by
    calc 1 - (n : ℝ) * y = 1 + n * (-y) := by ring
      _ ≤ (1 + -y) ^ n := one_add_mul_le_pow (by linarith) n
      _ = (1 - y) ^ n := by ring
  have hle1 : (1 - y) ^ n ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
  have htail0 : 0 ≤ ∑ v ∈ (Bset n).filter (fun v => ¬ absv v < 3 * n), ((1 : ℝ) / 2) ^ absv v :=
    Finset.sum_nonneg (fun _ _ => by positivity)
  have hT : ∑ v ∈ Tset n, ((1 : ℝ) / 2) ^ absv v =
      ∑ v ∈ (Bset n).filter (fun v => absv v < 3 * n), ((1 : ℝ) / 2) ^ absv v := rfl
  constructor <;> linarith



/-! Prop 1.9 assembly for a general finitely supported weight `w` on odd numbers. -/
open Classical in
/-- `P(Q(N))` for the (sub)probability weight `w` on the finite set `S`. -/
noncomputable def pm (S : Finset ℕ) (w : ℕ → ℝ) (Q : ℕ → Prop) : ℝ :=
  ∑ N ∈ S, if Q N then w N else 0


lemma pm_congr (S : Finset ℕ) (w : ℕ → ℝ) {Q Q' : ℕ → Prop} (h : ∀ N ∈ S, Q N ↔ Q' N) :
    pm S w Q = pm S w Q' := by
  unfold pm
  refine Finset.sum_congr rfl (fun N hN => ?_)
  by_cases hq : Q N
  · rw [if_pos hq, if_pos ((h N hN).1 hq)]
  · rw [if_neg hq, if_neg (fun h' => hq ((h N hN).2 h'))]


lemma pm_split (S : Finset ℕ) (w : ℕ → ℝ) (Q R : ℕ → Prop) :
    pm S w Q = pm S w (fun N => Q N ∧ R N) + pm S w (fun N => Q N ∧ ¬ R N) := by
  unfold pm
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun N _ => ?_)
  by_cases hq : Q N <;> by_cases hr : R N <;> simp [hq, hr]


lemma pm_nonneg (S : Finset ℕ) (w : ℕ → ℝ) (hw : ∀ N ∈ S, 0 ≤ w N) (Q : ℕ → Prop) :
    0 ≤ pm S w Q := by
  unfold pm
  refine Finset.sum_nonneg (fun N hN => ?_)
  split_ifs
  · exact hw N hN
  · exact le_refl _


lemma pm_mono (S : Finset ℕ) (w : ℕ → ℝ) (hw : ∀ N ∈ S, 0 ≤ w N) {Q Q' : ℕ → Prop}
    (h : ∀ N ∈ S, Q N → Q' N) : pm S w Q ≤ pm S w Q' := by
  unfold pm
  refine Finset.sum_le_sum (fun N hN => ?_)
  by_cases hq : Q N
  · rw [if_pos hq, if_pos (h N hN hq)]
  · rw [if_neg hq]
    split_ifs
    · exact hw N hN
    · exact le_refl _


open Classical in
/-- Uniform odd residue mod `2^{3n}`: `P(a⃗^{(n)} = a⃗, a⃗ ∈ E ∩ T) = Σ 2^{-|a⃗|}`. -/
lemma U_vec_E (n : ℕ) (E : (Fin n → ℕ) → Prop) :
    (((Rset n).filter (fun r => E (vecn n r) ∧ vecn n r ∈ Tset n)).card : ℝ) / 2 ^ (3 * n - 1) =
      ∑ v ∈ (Tset n).filter E, ((1 : ℝ) / 2) ^ absv v := by
  rw [Finset.card_eq_sum_card_fiberwise (f := vecn n) (t := (Tset n).filter E) ?_]
  · push_cast
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl (fun v hv => ?_)
    have hvT := (Finset.mem_filter.1 hv).1
    have hfib : ((Rset n).filter (fun r => E (vecn n r) ∧ vecn n r ∈ Tset n)).filter
        (fun r => vecn n r = v) = (Rset n).filter (fun r => vecn n r = v) := by
      ext r
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨⟨h1, _⟩, h2⟩; exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩
        refine ⟨⟨h1, ?_, ?_⟩, h2⟩
        · rw [h2]; exact (Finset.mem_filter.1 hv).2
        · rw [h2]; exact hvT
    rw [hfib, card_vecn_eq n v hvT]
    have hs := Tset_abs hvT
    have : (2 : ℝ) ^ (3 * n - 1) = 2 ^ (3 * n - (absv v + 1)) * 2 ^ absv v := by
      rw [← pow_add]; congr 1; omega
    rw [this, one_div_pow]
    push_cast
    field_simp
  · intro r hr
    have := (Finset.mem_filter.1 hr).2
    exact Finset.mem_filter.2 ⟨this.2, this.1⟩


open Classical in
/-- Uniform odd residue mod `2^{3n}`: `P(|a⃗^{(n)}| ≥ 3n) ≤ n 2^{-3n} + (8/9)^n` (Lemma 4.1 at `n' = 3n`). -/
lemma U_tail (n : ℕ) (hn : 1 ≤ n) :
    (((Rset n).filter (fun r => vecn n r ∉ Tset n)).card : ℝ) / 2 ^ (3 * n - 1) ≤
      (n : ℝ) * (1 / 2) ^ (3 * n) + (8 / 9) ^ n := by
  have hT : (((Rset n).filter (fun r => vecn n r ∈ Tset n)).card : ℝ) / 2 ^ (3 * n - 1) =
      ∑ v ∈ Tset n, ((1 : ℝ) / 2) ^ absv v := by
    have h := U_vec_E n (fun _ => True)
    convert h using 4
    all_goals (try ext)
    all_goals simp
  have hc := Finset.card_filter_add_card_filter_not (s := Rset n) (fun r => vecn n r ∈ Tset n)
  rw [card_Rset n hn] at hc
  have hc' : (((Rset n).filter (fun r => vecn n r ∉ Tset n)).card : ℝ) =
      2 ^ (3 * n - 1) - ((Rset n).filter (fun r => vecn n r ∈ Tset n)).card := by
    have : (((Rset n).filter (fun r => vecn n r ∈ Tset n)).card : ℝ) +
        ((Rset n).filter (fun r => vecn n r ∉ Tset n)).card = 2 ^ (3 * n - 1) := by
      exact_mod_cast hc
    linarith
  rw [hc', sub_div, div_self (by positivity), hT]
  linarith [(geomT_bounds n).1]


lemma small_terms (n : ℕ) :
    ((1 : ℝ) / 2) ^ (3 * n) ≤ (8 / 9) ^ n ∧ (n : ℝ) * (1 / 2) ^ (3 * n) ≤ (8 / 9) ^ n := by
  have hy : ((1 : ℝ) / 2) ^ (3 * n) = (1 / 8) ^ n := by rw [pow_mul]; norm_num
  have h2n' : n < 2 ^ n := by
    first | exact Nat.lt_two_pow_self | exact Nat.lt_two_pow n | exact n.lt_two_pow_self
  have h2n : (n : ℝ) ≤ 2 ^ n := by exact_mod_cast h2n'.le
  rw [hy]
  constructor
  · exact pow_le_pow_left₀ (by norm_num) (by norm_num) n
  · calc (n : ℝ) * (1 / 8) ^ n ≤ 2 ^ n * (1 / 8) ^ n :=
          mul_le_mul_of_nonneg_right h2n (by positivity)
      _ = (1 / 4) ^ n := by rw [← mul_pow]; norm_num
      _ ≤ (8 / 9) ^ n := pow_le_pow_left₀ (by norm_num) (by norm_num) n


open Classical in
/-- **Tao Proposition 1.9** (with `n' = 3n`, event form). If the weight `w` on odd numbers makes
`N mod 2^{3n}` uniform on odd residues up to `K 2^{-3n}` in every event, then the first `n`
Syracuse valuations are `Geom(2)^n`-distributed up to `(2K+2)(8/9)^n` in every event. -/
theorem prop19 (n : ℕ) (hn : 1 ≤ n) (S : Finset ℕ) (w : ℕ → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hodd : ∀ N ∈ S, Odd N) (hw : ∀ N ∈ S, 0 ≤ w N)
    (hU : ∀ P : ℕ → Prop, |pm S w (fun N => P (N % 2 ^ (3 * n))) -
      (((Rset n).filter P).card : ℝ) / 2 ^ (3 * n - 1)| ≤ K * (1 / 2) ^ (3 * n))
    (E : (Fin n → ℕ) → Prop) :
    |pm S w (fun N => E (vecn n N)) - ∑ v ∈ (Tset n).filter E, ((1 : ℝ) / 2) ^ absv v| ≤
      (2 * K + 2) * (8 / 9) ^ n := by
  have hmododd : ∀ N ∈ S, Odd (N % 2 ^ (3 * n)) := by
    intro N hN
    rw [Nat.odd_iff, Nat.mod_mod_of_dvd _ (dvd_pow_self 2 (by omega))]
    exact Nat.odd_iff.1 (hodd N hN)
  have hTiff : ∀ N ∈ S, (vecn n N ∈ Tset n ↔ vecn n (N % 2 ^ (3 * n)) ∈ Tset n) ∧
      (vecn n N ∈ Tset n → vecn n (N % 2 ^ (3 * n)) = vecn n N) := by
    intro N hN
    have hm : N % 2 ^ (3 * n) = (N % 2 ^ (3 * n)) % 2 ^ (3 * n) := (Nat.mod_mod _ _).symm
    refine ⟨⟨fun h => ?_, fun h => ?_⟩,
      fun h => vecn_transfer n N _ (hodd N hN) (hmododd N hN) hm h⟩
    · rwa [vecn_transfer n N _ (hodd N hN) (hmododd N hN) hm h]
    · rwa [vecn_transfer n (N % 2 ^ (3 * n)) N (hmododd N hN) (hodd N hN) hm.symm h]
  have h1 : pm S w (fun N => E (vecn n N) ∧ vecn n N ∈ Tset n) =
      pm S w (fun N => E (vecn n (N % 2 ^ (3 * n))) ∧ vecn n (N % 2 ^ (3 * n)) ∈ Tset n) := by
    apply pm_congr
    intro N hN
    constructor
    · rintro ⟨hE, hT⟩
      exact ⟨by rw [(hTiff N hN).2 hT]; exact hE, (hTiff N hN).1.1 hT⟩
    · rintro ⟨hE, hT⟩
      have hT' := (hTiff N hN).1.2 hT
      exact ⟨by rw [← (hTiff N hN).2 hT']; exact hE, hT'⟩
  have h2 : pm S w (fun N => vecn n N ∉ Tset n) =
      pm S w (fun N => vecn n (N % 2 ^ (3 * n)) ∉ Tset n) := by
    apply pm_congr
    intro N hN
    exact not_congr (hTiff N hN).1
  have hU' : ∀ (P : ℕ → Prop) [DecidablePred P], |pm S w (fun N => P (N % 2 ^ (3 * n))) -
      (((Rset n).filter P).card : ℝ) / 2 ^ (3 * n - 1)| ≤ K * (1 / 2) ^ (3 * n) := by
    intro P _
    convert hU P
  have hU1 := hU' (fun r => E (vecn n r) ∧ vecn n r ∈ Tset n)
  have hU2 := hU' (fun r => vecn n r ∉ Tset n)
  beta_reduce at hU1 hU2
  rw [← h1, U_vec_E] at hU1
  rw [← h2] at hU2
  have htail := U_tail n hn
  have hsplit := pm_split S w (fun N => E (vecn n N)) (fun N => vecn n N ∈ Tset n)
  have hle : pm S w (fun N => E (vecn n N) ∧ ¬ vecn n N ∈ Tset n) ≤
      pm S w (fun N => vecn n N ∉ Tset n) := pm_mono S w hw (fun N _ h => h.2)
  have h0 := pm_nonneg S w hw (fun N => E (vecn n N) ∧ ¬ vecn n N ∈ Tset n)
  obtain ⟨hs1, hs2⟩ := small_terms n
  have hU2' := (abs_le.1 hU2).2
  have hU1' := abs_le.1 hU1
  rw [abs_le]
  constructor <;> nlinarith


lemma class_sum_blocks (f : ℕ → ℝ) (a b M r : ℕ) (hM : 0 < M) (hr : r < M) :
    ∑ N ∈ (Finset.Icc a b).filter (fun N => N % M = r), f N =
      ∑ j ∈ Finset.range (b / M + 1),
        if a ≤ j * M + r ∧ j * M + r ≤ b then f (j * M + r) else 0 := by
  rw [← Finset.sum_filter]
  symm
  apply Finset.sum_nbij' (fun j => j * M + r) (fun N => N / M)
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc] at hj ⊢
    refine ⟨hj.2, ?_⟩
    rw [Nat.add_mod, Nat.mul_mod_left, zero_add, Nat.mod_mod, Nat.mod_eq_of_lt hr]
  · intro N hN
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc] at hN ⊢
    have hd := Nat.div_add_mod N M
    rw [hN.2] at hd
    have hN' : N / M * M + r = N := by rw [mul_comm]; exact hd
    rw [hN']
    exact ⟨Nat.lt_succ_of_le (Nat.div_le_div_right hN.1.2), hN.1⟩
  · intro j _
    rw [add_comm, Nat.add_mul_div_right _ _ hM, Nat.div_eq_of_lt hr, zero_add]
  · intro N hN
    simp only [Finset.mem_filter] at hN
    have hd := Nat.div_add_mod N M
    rw [hN.2] at hd
    rw [mul_comm]; exact hd
  · intro j _
    rfl


lemma class_sum_close (f : ℕ → ℝ) (hf : ∀ m n, 1 ≤ m → m ≤ n → f n ≤ f m) (hf0 : ∀ n, 0 ≤ f n)
    (a b M r r' : ℕ) (hM : 0 < M) (hr : r < M) (hr' : r' < M) (haM : M ≤ a) :
    |∑ N ∈ (Finset.Icc a b).filter (fun N => N % M = r), f N -
      ∑ N ∈ (Finset.Icc a b).filter (fun N => N % M = r'), f N| ≤ f (a / M * M) + 2 * f a := by
  rw [class_sum_blocks f a b M r hM hr, class_sum_blocks f a b M r' hM hr',
    ← Finset.sum_sub_distrib]
  obtain ⟨j0, hj0⟩ : ∃ j0, j0 = a / M := ⟨_, rfl⟩
  rw [← hj0]
  have hj01 : 1 ≤ j0 := by
    rw [hj0]; exact (Nat.one_le_div_iff hM).2 haM
  let g : ℕ → ℝ := fun j => if j0 ≤ j then f (j * M) - f ((j + 1) * M) else 0
  have hjM : ∀ j, j0 ≤ j → 1 ≤ j * M := fun j hj =>
    Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  have hg0 : ∀ j, 0 ≤ g j := by
    intro j
    simp only [g]
    split_ifs with h
    · linarith [hf (j * M) ((j + 1) * M) (hjM j h) (by nlinarith)]
    · exact le_refl _
  have hone : ∀ j s s', s < M → s' < M → (a ≤ j * M + s ∧ j * M + s ≤ b) →
      ¬ (a ≤ j * M + s' ∧ j * M + s' ≤ b) → j = j0 ∨ j = b / M := by
    intro j s s' hs hs' h hn
    have hsucc : (j + 1) * M = j * M + M := by ring
    by_cases h3 : a ≤ j * M + s'
    · right
      have h4 : b < j * M + s' := by
        by_contra h5; exact hn ⟨h3, by omega⟩
      exact (Nat.div_eq_of_lt_le (by omega) (by rw [hsucc]; omega)).symm
    · left
      rw [hj0]
      exact (Nat.div_eq_of_lt_le (by omega) (by rw [hsucc]; omega)).symm
  have hpt : ∀ j, |(if a ≤ j * M + r ∧ j * M + r ≤ b then f (j * M + r) else 0) -
      (if a ≤ j * M + r' ∧ j * M + r' ≤ b then f (j * M + r') else 0)| ≤
      g j + ((if j = j0 then f a else 0) + (if j = b / M then f a else 0)) := by
    intro j
    have hfa : ∀ s, a ≤ j * M + s → f (j * M + s) ≤ f a := fun s hs => hf a _ (by omega) hs
    have hite0 : 0 ≤ (if j = j0 then f a else 0) := by split_ifs <;> simp [hf0]
    have hite1 : 0 ≤ (if j = b / M then f a else 0) := by split_ifs <;> simp [hf0]
    have hboth : ∀ s, s < M → a ≤ j * M + s → j0 ≤ j := by
      intro s hs h
      rw [hj0]
      have : a < (j + 1) * M := by nlinarith
      exact Nat.lt_succ_iff.1 ((Nat.div_lt_iff_lt_mul hM).2 this)
    have hrhs : ∀ s, s < M → a ≤ j * M + s → f (j * M + s) ≤
        (if j = j0 then f a else 0) + (if j = b / M then f a else 0) → True := fun _ _ _ _ => trivial
    by_cases hp : a ≤ j * M + r ∧ j * M + r ≤ b <;> by_cases hp' : a ≤ j * M + r' ∧ j * M + r' ≤ b
    · rw [if_pos hp, if_pos hp']
      have hj := hboth r hr hp.1
      have hgj : g j = f (j * M) - f ((j + 1) * M) := by simp only [g]; rw [if_pos hj]
      have h1 := hjM j hj
      have e1 := hf (j * M) (j * M + r) h1 (by omega)
      have e2 := hf (j * M) (j * M + r') h1 (by omega)
      have e3 := hf (j * M + r) ((j + 1) * M) (by omega) (by nlinarith)
      have e4 := hf (j * M + r') ((j + 1) * M) (by omega) (by nlinarith)
      rw [abs_sub_le_iff]
      constructor <;> linarith
    · rw [if_pos hp, if_neg hp', sub_zero, abs_of_nonneg (hf0 _)]
      have := hfa r hp.1
      rcases hone j r r' hr hr' hp hp' with h | h
      · rw [if_pos h]; linarith [hg0 j]
      · rw [if_pos h]; linarith [hg0 j]
    · rw [if_neg hp, if_pos hp', zero_sub, abs_neg, abs_of_nonneg (hf0 _)]
      have := hfa r' hp'.1
      rcases hone j r' r hr' hr hp' hp with h | h
      · rw [if_pos h]; linarith [hg0 j]
      · rw [if_pos h]; linarith [hg0 j]
    · rw [if_neg hp, if_neg hp', sub_zero, abs_zero]
      linarith [hg0 j]
  have htel : ∀ n, ∑ j ∈ Finset.range n, g j ≤ f (j0 * M) := by
    have key : ∀ n, ∑ j ∈ Finset.range n, g j =
        if n ≤ j0 then 0 else f (j0 * M) - f (n * M) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [Finset.sum_range_succ, ih]
        simp only [g]
        split_ifs <;> first
          | ring1
          | (exfalso; omega)
          | (rw [show n = j0 by omega]; ring1)
    intro n
    rw [key]
    split_ifs
    · exact hf0 _
    · linarith [hf0 (n * M)]
  have hsum1 : ∑ j ∈ Finset.range (b / M + 1), (if j = j0 then f a else 0) ≤ f a := by
    rw [Finset.sum_ite_eq']; split_ifs <;> simp [hf0]
  have hsum2 : ∑ j ∈ Finset.range (b / M + 1), (if j = b / M then f a else 0) ≤ f a := by
    rw [Finset.sum_ite_eq']; split_ifs <;> simp [hf0]
  calc _ ≤ ∑ j ∈ Finset.range (b / M + 1), |(if a ≤ j * M + r ∧ j * M + r ≤ b then f (j * M + r) else 0) -
        (if a ≤ j * M + r' ∧ j * M + r' ≤ b then f (j * M + r') else 0)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range (b / M + 1),
        (g j + ((if j = j0 then f a else 0) + (if j = b / M then f a else 0))) :=
        Finset.sum_le_sum (fun j _ => hpt j)
    _ = ∑ j ∈ Finset.range (b / M + 1), g j +
        (∑ j ∈ Finset.range (b / M + 1), (if j = j0 then f a else 0) +
          ∑ j ∈ Finset.range (b / M + 1), (if j = b / M then f a else 0)) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    _ ≤ f (j0 * M) + 2 * f a := by linarith [htel (b / M + 1)]


/-! DECOMPOSE item 5, Section 3 telescoping. -/
/-! DECOMPOSE item 5c support: the support of `N_y` is nonempty for `y ≥ 1000`. -/
/-! DECOMPOSE item 5c: per-interval bound. -/
/-! DECOMPOSE item 5d: covering `(M, x]` by the intervals `[W_{j+1}, W_j]`, `W_j = x^{α^{-j}}`. -/
/-! DECOMPOSE item 4b: hypothesis (1.11) of Prop 1.9 for the log-uniform variable `N_y`. -/
/-- Averaging: if all values `s r` (`r ∈ R`) are within `δ` of each other, the share of a
subfamily `F ⊆ R` in the total is within `#R δ / Σ s` of `#F / #R`. -/
lemma avg_close (R F : Finset ℕ) (hF : F ⊆ R) (s : ℕ → ℝ) (δ : ℝ)
    (hδ : ∀ r ∈ R, ∀ r' ∈ R, |s r - s r'| ≤ δ) (hR : 0 < R.card) (hZ : 0 < ∑ r ∈ R, s r) :
    |(∑ r ∈ F, s r) / (∑ r ∈ R, s r) - (F.card : ℝ) / R.card| ≤
      R.card * δ / ∑ r ∈ R, s r := by
  set Z := ∑ r ∈ R, s r with hZdef
  have hc : (0 : ℝ) < R.card := by exact_mod_cast hR
  have hδ0 : 0 ≤ δ := by
    obtain ⟨r, hr⟩ := Finset.card_pos.mp hR
    simpa using hδ r hr r hr
  have hFc : (F.card : ℝ) ≤ R.card := by exact_mod_cast Finset.card_le_card hF
  have hin : ∀ r, ∑ r' ∈ R, (s r - s r') = R.card * s r - Z := fun r => by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  have key : ∑ r ∈ F, ∑ r' ∈ R, (s r - s r') = R.card * ∑ r ∈ F, s r - F.card * Z := by
    rw [Finset.sum_congr rfl (fun r _ => hin r), Finset.sum_sub_distrib, Finset.sum_const,
      nsmul_eq_mul, ← Finset.mul_sum]
  have habs : |∑ r ∈ F, ∑ r' ∈ R, (s r - s r')| ≤ F.card * (R.card * δ) := by
    calc |∑ r ∈ F, ∑ r' ∈ R, (s r - s r')|
        ≤ ∑ r ∈ F, |∑ r' ∈ R, (s r - s r')| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ r ∈ F, ∑ r' ∈ R, |s r - s r'| :=
          Finset.sum_le_sum (fun r _ => Finset.abs_sum_le_sum_abs _ _)
      _ ≤ ∑ r ∈ F, ∑ r' ∈ R, δ :=
          Finset.sum_le_sum (fun r hr => Finset.sum_le_sum (fun r' hr' => hδ r (hF hr) r' hr'))
      _ = F.card * (R.card * δ) := by simp [Finset.sum_const, nsmul_eq_mul]
  have heq : (∑ r ∈ F, s r) / Z - F.card / R.card =
      (∑ r ∈ F, ∑ r' ∈ R, (s r - s r')) / (Z * R.card) := by
    rw [key]; field_simp
  rw [heq, abs_div, abs_of_pos (mul_pos hZ hc), div_le_iff₀ (mul_pos hZ hc)]
  have h2 : R.card * δ / Z * (Z * R.card) = R.card * (R.card * δ) := by field_simp
  rw [h2]
  exact habs.trans (mul_le_mul_of_nonneg_right hFc (by positivity))


/-- Residue-class sum of `1/N` over `[⌈y⌉, ⌊y^α⌋]`. -/
noncomputable def cs (y : ℝ) (M r : ℕ) : ℝ :=
  ∑ N ∈ (Finset.Icc ⌈y⌉₊ ⌊y ^ alph⌋₊).filter (fun N => N % M = r), (1 : ℝ) / N


lemma odd_of_mod_eq (n N r : ℕ) (hn : 1 ≤ n) (h : N % 2 ^ (3 * n) = r) (hr : Odd r) : Odd N := by
  have h2 : N % 2 ^ (3 * n) % 2 = N % 2 := Nat.mod_mod_of_dvd N (dvd_pow_self 2 (by omega))
  rw [h] at h2
  exact Nat.odd_iff.2 (h2 ▸ Nat.odd_iff.1 hr)


lemma odd_mod (n N : ℕ) (hn : 1 ≤ n) (hN : Odd N) : Odd (N % 2 ^ (3 * n)) := by
  rw [Nat.odd_iff, Nat.mod_mod_of_dvd _ (dvd_pow_self 2 (by omega))]
  exact Nat.odd_iff.1 hN


open Classical in
lemma sum_oddIcc_mod (y : ℝ) (n : ℕ) (hn : 1 ≤ n) (P : ℕ → Prop) :
    ∑ N ∈ oddIcc y, (if P (N % 2 ^ (3 * n)) then (1 : ℝ) / N else 0) =
      ∑ r ∈ (Rset n).filter P, cs y (2 ^ (3 * n)) r := by
  rw [← Finset.sum_filter]
  have hmaps : ∀ N ∈ (oddIcc y).filter (fun N => P (N % 2 ^ (3 * n))),
      N % 2 ^ (3 * n) ∈ (Rset n).filter P := by
    intro N hN
    simp only [oddIcc, Finset.mem_filter] at hN
    simp only [Rset, Finset.mem_filter, Finset.mem_range]
    exact ⟨⟨Nat.mod_lt _ (by positivity), odd_mod n N hn hN.1.2⟩, hN.2⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  apply Finset.sum_congr rfl
  intro r hr
  simp only [Rset, Finset.mem_filter, Finset.mem_range] at hr
  unfold cs
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext N
  simp only [oddIcc, Finset.mem_filter]
  constructor
  · rintro ⟨⟨⟨h1, _⟩, _⟩, h3⟩
    exact ⟨h1, h3⟩
  · rintro ⟨h1, h3⟩
    exact ⟨⟨⟨h1, odd_of_mod_eq n N r hn h3 hr.1.2⟩, h3 ▸ hr.2⟩, h3⟩


open Classical in
lemma Z_eq_cs (y : ℝ) (n : ℕ) (hn : 1 ≤ n) : Z y = ∑ r ∈ Rset n, cs y (2 ^ (3 * n)) r := by
  have h := sum_oddIcc_mod y n hn (fun _ => True)
  calc Z y = ∑ N ∈ oddIcc y, (if True then (1 : ℝ) / N else 0) := by unfold Z; simp
    _ = ∑ r ∈ (Rset n).filter (fun _ => True), cs y (2 ^ (3 * n)) r := by convert h
    _ = ∑ r ∈ Rset n, cs y (2 ^ (3 * n)) r := by congr 1; ext r; simp


lemma cs_close (y : ℝ) (n : ℕ) (hM : 2 * 2 ^ (3 * n) ≤ ⌈y⌉₊) (r r' : ℕ)
    (hr : r < 2 ^ (3 * n)) (hr' : r' < 2 ^ (3 * n)) :
    |cs y (2 ^ (3 * n)) r - cs y (2 ^ (3 * n)) r'| ≤ 4 / (⌈y⌉₊ : ℝ) := by
  set M := 2 ^ (3 * n) with hMdef
  set a := ⌈y⌉₊ with hadef
  have hM0 : 0 < M := by positivity
  have h := class_sum_close (fun N => (1 : ℝ) / N)
    (fun m k hm hmk => one_div_le_one_div_of_le (by exact_mod_cast hm) (by exact_mod_cast hmk))
    (fun k => by positivity) a ⌊y ^ alph⌋₊ M r r' hM0 hr hr' (by omega)
  unfold cs
  refine h.trans ?_
  have hdm := Nat.div_add_mod' a M
  have hml := Nat.mod_lt a hM0
  have hq : a ≤ 2 * (a / M * M) := by omega
  have hqpos : 0 < a / M * M := by omega
  have ha0 : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by omega)
  have h1 : (1 : ℝ) / ((a / M * M : ℕ) : ℝ) ≤ 2 / a := by
    rw [div_le_div_iff₀ (by exact_mod_cast hqpos) ha0]
    have : (a : ℝ) ≤ 2 * ((a / M * M : ℕ) : ℝ) := by exact_mod_cast hq
    linarith
  have h2 : 2 * ((1 : ℝ) / a) = 2 / a := by ring
  have h3 : (2 : ℝ) / a + 2 / a = 4 / a := by ring
  show (1 : ℝ) / ((a / M * M : ℕ) : ℝ) + 2 * (1 / (a : ℝ)) ≤ 4 / a
  linarith


open Classical in
/-- Hypothesis (1.11) of Prop 1.9 for `N_y` (Tao (5.4)), with explicit constant. -/
theorem Ny_hU (y : ℝ) (n : ℕ) (hn : 1 ≤ n) (hM : 2 * 2 ^ (3 * n) ≤ ⌈y⌉₊) (hZ : 0 < Z y)
    (P : ℕ → Prop) :
    |pm (oddIcc y) (fun N => 1 / (N : ℝ) / Z y) (fun N => P (N % 2 ^ (3 * n))) -
      (((Rset n).filter P).card : ℝ) / 2 ^ (3 * n - 1)| ≤
      (2 ^ (6 * n + 1) / ((⌈y⌉₊ : ℝ) * Z y)) * (1 / 2) ^ (3 * n) := by
  have hpm : pm (oddIcc y) (fun N => 1 / (N : ℝ) / Z y) (fun N => P (N % 2 ^ (3 * n))) =
      (∑ r ∈ (Rset n).filter P, cs y (2 ^ (3 * n)) r) / ∑ r ∈ Rset n, cs y (2 ^ (3 * n)) r := by
    rw [← sum_oddIcc_mod y n hn P, ← Z_eq_cs y n hn]
    unfold pm
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro N _
    split_ifs <;> simp
  have hcard := card_Rset n hn
  have hRc : 0 < (Rset n).card := by rw [hcard]; positivity
  have hZ' : 0 < ∑ r ∈ Rset n, cs y (2 ^ (3 * n)) r := by rw [← Z_eq_cs y n hn]; exact hZ
  have h := avg_close (Rset n) ((Rset n).filter P) (Finset.filter_subset _ _)
    (cs y (2 ^ (3 * n))) (4 / (⌈y⌉₊ : ℝ))
    (fun r hr r' hr' => cs_close y n hM r r'
      (Finset.mem_range.1 (Finset.mem_filter.1 hr).1)
      (Finset.mem_range.1 (Finset.mem_filter.1 hr').1)) hRc hZ'
  rw [← Z_eq_cs y n hn, hcard] at h
  rw [hpm, ← Z_eq_cs y n hn]
  have hcast : (((2 ^ (3 * n - 1) : ℕ)) : ℝ) = (2 : ℝ) ^ (3 * n - 1) := by push_cast; ring
  rw [hcast] at h
  refine h.trans (le_of_eq ?_)
  have ha0 : (0 : ℝ) < ⌈y⌉₊ := by
    have : 0 < ⌈y⌉₊ := by have := Nat.one_le_two_pow (n := 3 * n); omega
    exact_mod_cast this
  obtain ⟨m, hm⟩ : ∃ m, 3 * n = m + 1 := ⟨3 * n - 1, by omega⟩
  have hm1 : 3 * n - 1 = m := by omega
  have hm2 : 6 * n + 1 = 2 * m + 3 := by omega
  rw [hm1, hm2, hm, one_div_pow]
  field_simp
  ring


lemma prob_eq_pm (y : ℝ) (Q : ℕ → Prop) :
    prob y Q = pm (oddIcc y) (fun N => 1 / (N : ℝ) / Z y) Q := by
  unfold prob pm
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro N _
  split_ifs <;> simp


open Classical in
/-- Prop 1.9 for `N_y` (Tao (5.4)-(5.5)): the valuation vector of `N_y` is close to Geom(2)^n. -/
theorem prop19_Ny (y : ℝ) (n : ℕ) (hn : 1 ≤ n) (hM : 2 * 2 ^ (3 * n) ≤ ⌈y⌉₊) (hZ : 0 < Z y)
    (E : (Fin n → ℕ) → Prop) :
    |prob y (fun N => E (vecn n N)) - ∑ v ∈ (Tset n).filter E, ((1 : ℝ) / 2) ^ absv v| ≤
      (2 * (2 ^ (6 * n + 1) / ((⌈y⌉₊ : ℝ) * Z y)) + 2) * (8 / 9) ^ n := by
  have ha0 : (0 : ℝ) < ⌈y⌉₊ := by
    have : 0 < ⌈y⌉₊ := by have := Nat.one_le_two_pow (n := 3 * n); omega
    exact_mod_cast this
  rw [prob_eq_pm]
  exact prop19 n hn (oddIcc y) (fun N => 1 / (N : ℝ) / Z y) _ (by positivity)
    (fun N hN => (Finset.mem_filter.1 hN).2) (fun N _ => div_nonneg (by positivity) hZ.le)
    (Ny_hU y n hn hM hZ) E



set_option autoImplicit false
lemma box_gen (n K : ℕ) (z : ℝ) :
    ∑ w ∈ Box n K, ((1 : ℝ) / 2) ^ (∑ i, w i) * z ^ (∑ i, w i) =
      (∑ a ∈ Finset.Icc 1 K, (z / 2) ^ a) ^ n := by
  calc ∑ w ∈ Box n K, ((1 : ℝ) / 2) ^ (∑ i, w i) * z ^ (∑ i, w i)
      = ∑ w ∈ Box n K, ∏ i, (z / 2) ^ (w i) := by
        apply Finset.sum_congr rfl
        intro w _
        rw [Finset.prod_pow_eq_pow_sum, div_eq_mul_one_div z 2, mul_pow, mul_comm]
    _ = ∏ _i : Fin n, ∑ a ∈ Finset.Icc 1 K, (z / 2) ^ a := (Finset.prod_univ_sum _ _).symm
    _ = (∑ a ∈ Finset.Icc 1 K, (z / 2) ^ a) ^ n := Fin.prod_const n _


lemma geom_Icc_le (x : ℝ) (h0 : 0 ≤ x) (h1 : x < 1) (K : ℕ) :
    ∑ a ∈ Finset.Icc 1 K, x ^ a ≤ x / (1 - x) := by
  calc ∑ a ∈ Finset.Icc 1 K, x ^ a ≤ ∑ a ∈ Finset.Ico 1 (K + 1), x ^ a := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro a ha
          simp only [Finset.mem_Icc, Finset.mem_Ico] at ha ⊢
          omega
        · intro a _ _; positivity
    _ ≤ x ^ 1 / (1 - x) := geom_sum_Ico_le_of_lt_one h0 h1
    _ = x / (1 - x) := by rw [pow_one]


lemma tail_gen (n K : ℕ) (P : (Fin n → ℕ) → Prop) [DecidablePred P] (z s : ℝ) (hz : 0 < z)
    (hz2 : z < 2) (hP : ∀ w ∈ Box n K, P w → 1 ≤ z ^ (-s + ((∑ i, w i : ℕ) : ℝ))) :
    ∑ w ∈ (Box n K).filter P, ((1 : ℝ) / 2) ^ (∑ i, w i) ≤
      z ^ (-s) * ((z / 2) / (1 - z / 2)) ^ n := by
  have hx0 : 0 ≤ z / 2 := by positivity
  have hx1 : z / 2 < 1 := by linarith
  calc ∑ w ∈ (Box n K).filter P, ((1 : ℝ) / 2) ^ (∑ i, w i)
      ≤ ∑ w ∈ (Box n K).filter P, z ^ (-s) * (((1 : ℝ) / 2) ^ (∑ i, w i) * z ^ (∑ i, w i)) := by
        apply Finset.sum_le_sum
        intro w hw
        have hw' := Finset.mem_filter.1 hw
        have h1 := hP w hw'.1 hw'.2
        rw [Real.rpow_add hz, Real.rpow_natCast] at h1
        have hp : (0 : ℝ) ≤ ((1 : ℝ) / 2) ^ (∑ i, w i) := by positivity
        nlinarith
    _ ≤ ∑ w ∈ Box n K, z ^ (-s) * (((1 : ℝ) / 2) ^ (∑ i, w i) * z ^ (∑ i, w i)) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro w _ _; positivity
    _ = z ^ (-s) * (∑ a ∈ Finset.Icc 1 K, (z / 2) ^ a) ^ n := by rw [← Finset.mul_sum, box_gen]
    _ ≤ z ^ (-s) * ((z / 2) / (1 - z / 2)) ^ n := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact pow_le_pow_left₀ (Finset.sum_nonneg (fun a _ => by positivity))
          (geom_Icc_le _ hx0 hx1 K) n


lemma log_one_add_ge (d : ℝ) (h0 : 0 ≤ d) (h1 : d ≤ 1 / 6) :
    d - 3 / 2 * d ^ 2 ≤ Real.log (1 + d) := by
  have hab : |(-d)| < 1 := by rw [abs_neg, abs_of_nonneg h0]; linarith
  have h := Real.abs_log_sub_add_sum_range_le hab 1
  simp only [Finset.sum_range_one, zero_add, pow_one, Nat.cast_zero, div_one, sub_neg_eq_add,
    abs_neg, abs_of_nonneg h0] at h
  have hq : d ^ 2 / (1 - d) ≤ 3 / 2 * d ^ 2 := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have := (abs_le.1 h).1
  rw [add_comm] at this
  linarith


lemma neg_log_one_sub_le (d : ℝ) (h0 : 0 ≤ d) (h1 : d ≤ 1 / 6) :
    -Real.log (1 - d) ≤ d + 3 / 2 * d ^ 2 ∧ d ≤ -Real.log (1 - d) := by
  have hab : |d| < 1 := by rw [abs_of_nonneg h0]; linarith
  have h := Real.abs_log_sub_add_sum_range_le hab 1
  simp only [Finset.sum_range_one, zero_add, pow_one, Nat.cast_zero, div_one,
    abs_of_nonneg h0] at h
  have hq : d ^ 2 / (1 - d) ≤ 3 / 2 * d ^ 2 := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have hl : Real.log (1 - d) ≤ (1 - d) - 1 := Real.log_le_sub_one_of_pos (by linarith)
  constructor
  · have := (abs_le.1 h).1; linarith
  · linarith


open Classical in
/-- Tao Lemma 2.2, lower tail: `P(|a| ≤ 2n - t) ≤ exp(-t min(t/n,1)/24)`. -/
theorem chernoff_down (n K : ℕ) (hn : 1 ≤ n) (t : ℝ) (ht : 0 ≤ t) :
    ∑ w ∈ (Box n K).filter (fun w => ((∑ i, w i : ℕ) : ℝ) ≤ 2 * (n : ℝ) - t),
      ((1 : ℝ) / 2) ^ (∑ i, w i) ≤ Real.exp (-(t * min (t / n) 1) / 24) := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  set μ := min (t / n) 1 with hμ
  have hμ0 : 0 ≤ μ := le_min (div_nonneg ht (by linarith)) zero_le_one
  have hμ1 : μ ≤ 1 := min_le_right _ _
  have hμt : (n : ℝ) * μ ≤ t := by
    have : μ ≤ t / n := min_le_left _ _
    rw [le_div_iff₀ (by linarith)] at this; linarith
  set d := μ / 6 with hd
  have hd0 : 0 ≤ d := by positivity
  have hd1 : d ≤ 1 / 6 := by rw [hd]; linarith
  have hz : 0 < 1 - d := by linarith
  have hb := tail_gen n K (fun w => ((∑ i, w i : ℕ) : ℝ) ≤ 2 * (n : ℝ) - t) (1 - d)
    (2 * n - t) hz (by linarith) (by
      intro w _ hw
      apply Real.one_le_rpow_of_pos_of_le_one_of_nonpos hz (by linarith)
        (by linarith))
  refine hb.trans ?_
  have eqE : (1 - d) ^ (-(2 * (n : ℝ) - t)) * ((1 - d) / 2 / (1 - (1 - d) / 2)) ^ n =
      Real.exp ((-(2 * n - t)) * Real.log (1 - d) + n * (Real.log (1 - d) - Real.log (1 + d))) := by
    have e1 : (1 - d) / 2 / (1 - (1 - d) / 2) = (1 - d) / (1 + d) := by
      have h1 : (1 : ℝ) + d ≠ 0 := by linarith
      have h2 : (1 : ℝ) - d ≠ 0 := by linarith
      rw [div_div, div_eq_div_iff (by linarith) (by linarith)]; ring
    rw [e1, Real.rpow_def_of_pos hz, ← Real.exp_log (show 0 < ((1 - d) / (1 + d)) ^ n by
      apply pow_pos; apply div_pos <;> linarith), ← Real.exp_add, Real.log_pow,
      Real.log_div (by linarith) (by linarith)]
    ring_nf
  rw [eqE]
  · apply Real.exp_le_exp.2
    have l1 := log_one_add_ge d hd0 hd1
    obtain ⟨l2, l3⟩ := neg_log_one_sub_le d hd0 hd1
    have hnd : (n : ℝ) * d ≤ t / 6 := by rw [hd]; linarith
    set e := -Real.log (1 - d) - d with he
    have he0 : 0 ≤ e := by linarith
    have he1 : e ≤ 3 / 2 * d ^ 2 := by linarith
    have key : (-(2 * n - t)) * Real.log (1 - d) + n * (Real.log (1 - d) - Real.log (1 + d))
        = (n - t) * d + n * e - t * e - n * Real.log (1 + d) := by rw [he]; ring
    rw [key]
    have s1 : (n : ℝ) * (d - 3 / 2 * d ^ 2) ≤ n * Real.log (1 + d) :=
      mul_le_mul_of_nonneg_left l1 (by linarith)
    have s2 : (n : ℝ) * e ≤ n * (3 / 2 * d ^ 2) := mul_le_mul_of_nonneg_left he1 (by linarith)
    have s3 : (n : ℝ) * μ * μ ≤ t * μ := mul_le_mul_of_nonneg_right hμt hμ0
    have s5 : 0 ≤ t * e := mul_nonneg ht he0
    have s6 : 0 ≤ t * μ := mul_nonneg ht hμ0
    rw [hd] at s1 s2 ⊢
    nlinarith [s1, s2, s3, s5, s6]


open Classical in
/-- Item 6a2: lower tail at `|a| < 1.9 n` (Tao (5.5)): `P(10|a| < 19n) ≤ exp(-n/2400)`. -/
theorem box_tail19 (n K : ℕ) (hn : 1 ≤ n) :
    ∑ w ∈ (Box n K).filter (fun w => 10 * (∑ i, w i) < 19 * n), ((1 : ℝ) / 2) ^ (∑ i, w i) ≤
      Real.exp (-(n : ℝ) / 2400) := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hc := chernoff_down n K hn ((n : ℝ) / 10) (by positivity)
  have hmin : min (((n : ℝ) / 10) / n) 1 = 1 / 10 := by
    rw [div_div, mul_comm, ← div_div, div_self (by positivity)]; norm_num
  rw [hmin] at hc
  refine le_trans ?_ (le_of_le_of_eq hc (by congr 1; ring))
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro w hw
    rw [Finset.mem_filter] at hw ⊢
    refine ⟨hw.1, ?_⟩
    have h1 : ((10 * (∑ i, w i) : ℕ) : ℝ) < ((19 * n : ℕ) : ℝ) := by exact_mod_cast hw.2
    push_cast at h1 ⊢
    linarith
  · intro _ _ _; positivity



set_option autoImplicit false
lemma ps_succ (a : ℕ → ℕ) (j : ℕ) : ps a (j + 1) = ps a j + a j := rfl


lemma ps_mono (a : ℕ → ℕ) {i j : ℕ} (h : i ≤ j) : ps a i ≤ ps a j := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (Nat.le_add_right _ _)


lemma ps_congr (a b : ℕ → ℕ) (n : ℕ) (h : ∀ i < n, a i = b i) : ps a n = ps b n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [ps_succ, ps_succ, ih (fun i hi => h i (by omega)), h n (by omega)]


lemma Fnat_zero (a : ℕ → ℕ) : Fnat a 0 = 0 := by simp [Fnat]


lemma Fnat_succ (a : ℕ → ℕ) (n : ℕ) : Fnat a (n + 1) = 2 ^ a n * Fnat a n + 3 ^ n := by
  unfold Fnat
  rw [Finset.sum_range_succ, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro j hj
    have hj' : j + 1 ≤ n := Finset.mem_range.1 hj
    have hm := ps_mono a hj'
    have e : ps a (n + 1) - ps a (j + 1) = a n + (ps a n - ps a (j + 1)) := by
      rw [ps_succ]; omega
    rw [e, pow_add]; ring
  · simp


lemma Fnat_congr (a b : ℕ → ℕ) (n : ℕ) (h : ∀ i < n, a i = b i) : Fnat a n = Fnat b n := by
  induction n with
  | zero => simp [Fnat_zero]
  | succ n ih => rw [Fnat_succ, Fnat_succ, ih (fun i hi => h i (by omega)), h n (by omega)]


/-! Tao Lemma 2.2 (Chernoff bound for sums of Geom(2)), in the truncated box model. -/
open Classical in
/-- Tao Lemma 2.2, upper tail: `P(|a| ≥ 2n + t) ≤ exp(-t min(t/n,1)/24)`. -/
theorem chernoff_up (n K : ℕ) (hn : 1 ≤ n) (t : ℝ) (ht : 0 ≤ t) :
    ∑ w ∈ (Box n K).filter (fun w => 2 * (n : ℝ) + t ≤ ((∑ i, w i : ℕ) : ℝ)),
      ((1 : ℝ) / 2) ^ (∑ i, w i) ≤ Real.exp (-(t * min (t / n) 1) / 24) := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  set μ := min (t / n) 1 with hμ
  have hμ0 : 0 ≤ μ := le_min (div_nonneg ht (by linarith)) zero_le_one
  have hμ1 : μ ≤ 1 := min_le_right _ _
  have hμt : (n : ℝ) * μ ≤ t := by
    have : μ ≤ t / n := min_le_left _ _
    rw [le_div_iff₀ (by linarith)] at this; linarith
  set d := μ / 6 with hd
  have hd0 : 0 ≤ d := by positivity
  have hd1 : d ≤ 1 / 6 := by rw [hd]; linarith
  have hz : 0 < 1 + d := by linarith
  have hb := tail_gen n K (fun w => 2 * (n : ℝ) + t ≤ ((∑ i, w i : ℕ) : ℝ)) (1 + d)
    (2 * n + t) hz (by linarith) (by
      intro w _ hw
      apply Real.one_le_rpow (by linarith) (by linarith))
  refine hb.trans ?_
  have eqE : (1 + d) ^ (-(2 * (n : ℝ) + t)) * ((1 + d) / 2 / (1 - (1 + d) / 2)) ^ n =
      Real.exp ((-(2 * n + t)) * Real.log (1 + d) + n * (Real.log (1 + d) - Real.log (1 - d))) := by
    have e1 : (1 + d) / 2 / (1 - (1 + d) / 2) = (1 + d) / (1 - d) := by
      have h1 : (1 : ℝ) + d ≠ 0 := by linarith
      have h2 : (1 : ℝ) - d ≠ 0 := by linarith
      rw [div_div, div_eq_div_iff (by linarith) (by linarith)]; ring
    rw [e1, Real.rpow_def_of_pos hz, ← Real.exp_log (show 0 < ((1 + d) / (1 - d)) ^ n by
      apply pow_pos; apply div_pos <;> linarith), ← Real.exp_add, Real.log_pow,
      Real.log_div (by linarith) (by linarith)]
    ring_nf
  rw [eqE]
  · apply Real.exp_le_exp.2
    have l1 := log_one_add_ge d hd0 hd1
    have l2 := (neg_log_one_sub_le d hd0 hd1).1
    have s1 : (n + t) * (d - 3 / 2 * d ^ 2) ≤ (n + t) * Real.log (1 + d) :=
      mul_le_mul_of_nonneg_left l1 (by linarith)
    have s2 : (n : ℝ) * -Real.log (1 - d) ≤ n * (d + 3 / 2 * d ^ 2) :=
      mul_le_mul_of_nonneg_left l2 (by linarith)
    have s3 : (n : ℝ) * μ * μ ≤ t * μ := mul_le_mul_of_nonneg_right hμt hμ0
    have s4 : t * μ * μ ≤ t * μ := by nlinarith [mul_nonneg ht hμ0]
    rw [hd] at s1 s2 ⊢
    nlinarith [s1, s2, s3, s4]


/-! Block splitting of the offset (Tao (1.5), (1.23); used in Section 6 on the event `C_{k,l}`). -/
lemma ps_add (a : ℕ → ℕ) (p q : ℕ) : ps a (p + q) = ps a p + ps (fun i => a (p + i)) q := by
  induction q with
  | zero => rfl
  | succ q ih => rw [← add_assoc, ps_succ, ih, ps_succ, add_assoc]


lemma Fnat_add (a : ℕ → ℕ) (p q : ℕ) :
    Fnat a (p + q) = 2 ^ ps (fun i => a (p + i)) q * Fnat a p + 3 ^ p * Fnat (fun i => a (p + i)) q := by
  induction q with
  | zero => simp [Fnat_zero, ps]
  | succ q ih =>
    rw [← add_assoc, Fnat_succ, ih, ps_succ, Fnat_succ]
    simp only [pow_add]
    ring


/-- Splitting `syr` at `p`: `syr_{p+q}(a) = syr_p(a) + 3^p 2^{-a_{[1,p]}} syr_q(a_{p+1..})` in `ZMod (3^{p+q})`. -/
lemma syrZ_split (a : ℕ → ℕ) (p q : ℕ) :
    syrZ (p + q) a = (Fnat a p : ZMod (3 ^ (p + q))) * ((2 : ZMod (3 ^ (p + q)))⁻¹) ^ ps a p +
      3 ^ p * ((2 : ZMod (3 ^ (p + q)))⁻¹) ^ ps a p *
        ((Fnat (fun i => a (p + i)) q : ZMod (3 ^ (p + q))) *
          ((2 : ZMod (3 ^ (p + q)))⁻¹) ^ ps (fun i => a (p + i)) q) := by
  unfold syrZ
  rw [Fnat_add, ps_add, pow_add ((2 : ZMod (3 ^ (p + q)))⁻¹)]
  have h2 : (2 : ZMod (3 ^ (p + q))) ^ ps (fun i => a (p + i)) q *
      ((2 : ZMod (3 ^ (p + q)))⁻¹) ^ ps (fun i => a (p + i)) q = 1 := by
    rw [← mul_pow, two_mul_inv, one_pow]
  push_cast
  linear_combination ((Fnat a p : ZMod (3 ^ (p + q))) *
    ((2 : ZMod (3 ^ (p + q)))⁻¹) ^ ps a p) * h2


/-! Item 7d (S7): Plancherel on `ZMod (3^n)` and the Fourier form of `Osc`. -/
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


lemma ps_padv {k : ℕ} (u : Fin k → ℕ) : ps (padv u) k = ∑ i, u i := by
  rw [ps_eq_sum, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp [padv, i.isLt]


/-- Left / right blocks of a tuple of length `k + q`. -/
def lft {k q : ℕ} (w : Fin (k + q) → ℕ) : Fin k → ℕ := fun i => w (Fin.castAdd q i)

def rgt {k q : ℕ} (w : Fin (k + q) → ℕ) : Fin q → ℕ := fun i => w (Fin.natAdd k i)


lemma padv_lft {k q : ℕ} (w : Fin (k + q) → ℕ) (i : ℕ) (hi : i < k) :
    padv w i = padv (lft w) i := by
  unfold padv lft
  rw [dif_pos (by omega : i < k + q), dif_pos hi]
  rfl


lemma padv_rgt {k q : ℕ} (w : Fin (k + q) → ℕ) (i : ℕ) (hi : i < q) :
    padv w (k + i) = padv (rgt w) i := by
  unfold padv rgt
  rw [dif_pos (by omega : k + i < k + q), dif_pos hi]
  rfl


lemma mem_Box_iff {k q K : ℕ} (w : Fin (k + q) → ℕ) :
    w ∈ Box (k + q) K ↔ lft w ∈ Box k K ∧ rgt w ∈ Box q K := by
  simp only [Box, Fintype.mem_piFinset, lft, rgt]
  constructor
  · intro h; exact ⟨fun i => h _, fun i => h _⟩
  · rintro ⟨h1, h2⟩ i
    induction i using Fin.addCases with
    | left j => exact h1 j
    | right j => exact h2 j


lemma lft_append {k q : ℕ} (u : Fin k → ℕ) (v : Fin q → ℕ) : lft (Fin.append u v) = u := by
  funext i; simp [lft]


lemma rgt_append {k q : ℕ} (u : Fin k → ℕ) (v : Fin q → ℕ) : rgt (Fin.append u v) = v := by
  funext i; simp [rgt]


lemma append_lft_rgt {k q : ℕ} (w : Fin (k + q) → ℕ) : Fin.append (lft w) (rgt w) = w :=
  Fin.append_castAdd_natAdd


lemma sum_lft_rgt {k q : ℕ} (w : Fin (k + q) → ℕ) : ∑ i, w i = ∑ i, lft w i + ∑ i, rgt w i :=
  Fin.sum_univ_add w


/-- Tao (1.5) on tuples: `syr_{k+q}(w) = syr_k(u) + 3^k 2^{-|u|} syr_q(v)` for `w = (u, v)`. -/
lemma syrZ_lr {k q : ℕ} (w : Fin (k + q) → ℕ) :
    syrZ (k + q) (padv w) = (Fnat (padv (lft w)) k : ZMod (3 ^ (k + q))) *
        ((2 : ZMod (3 ^ (k + q)))⁻¹) ^ ps (padv (lft w)) k +
      3 ^ k * ((2 : ZMod (3 ^ (k + q)))⁻¹) ^ ps (padv (lft w)) k *
        ((Fnat (padv (rgt w)) q : ZMod (3 ^ (k + q))) *
          ((2 : ZMod (3 ^ (k + q)))⁻¹) ^ ps (padv (rgt w)) q) := by
  rw [syrZ_split (padv w) k q,
    Fnat_congr (padv w) (padv (lft w)) k (fun i hi => padv_lft w i hi),
    ps_congr (padv w) (padv (lft w)) k (fun i hi => padv_lft w i hi),
    Fnat_congr (fun i => padv w (k + i)) (padv (rgt w)) q (fun i hi => padv_rgt w i hi),
    ps_congr (fun i => padv w (k + i)) (padv (rgt w)) q (fun i hi => padv_rgt w i hi)]


end Fact
section Fsq
open Finset
open Classical
end Fsq
section Red7h
open Finset
open Classical
lemma castHom_two_inv_gen {a b : ℕ} (h : 3 ^ a ∣ 3 ^ b) :
    ZMod.castHom h (ZMod (3 ^ a)) ((2 : ZMod (3 ^ b))⁻¹) = (2 : ZMod (3 ^ a))⁻¹ := by
  set φ := ZMod.castHom h (ZMod (3 ^ a))
  have h2 := congrArg φ (two_mul_inv b)
  rw [map_mul, map_one, map_ofNat] at h2
  calc φ (2 : ZMod (3 ^ b))⁻¹
        = φ (2 : ZMod (3 ^ b))⁻¹ * (2 * (2 : ZMod (3 ^ a))⁻¹) := by
          rw [two_mul_inv, mul_one]
    _ = (2 * φ (2 : ZMod (3 ^ b))⁻¹) * (2 : ZMod (3 ^ a))⁻¹ := by ring
    _ = (2 : ZMod (3 ^ a))⁻¹ := by rw [h2, one_mul]


lemma three_pow_self_zmod (n : ℕ) : (3 : ZMod (3 ^ n)) ^ n = 0 := by
  have h := ZMod.natCast_self (3 ^ n)
  rw [Nat.cast_pow, Nat.cast_ofNat] at h
  exact h


lemma box_mass_le_syr (j K : ℕ) : ∑ v ∈ Box j K, ((1 : ℝ) / 2) ^ (∑ i, v i) ≤ 1 := by
  have h := box_gen j K 1
  simp only [one_pow, mul_one] at h
  rw [h]
  have hg := geom_Icc_le ((1 : ℝ) / 2) (by norm_num) (by norm_num) K
  have hg' : ∑ a ∈ Finset.Icc 1 K, ((1 : ℝ) / 2) ^ a ≤ 1 := by
    have : (1 : ℝ) / 2 / (1 - 1 / 2) = 1 := by norm_num
    linarith
  have h0 : 0 ≤ ∑ a ∈ Finset.Icc 1 K, ((1 : ℝ) / 2) ^ a := by positivity
  exact pow_le_one₀ h0 hg'


end Red7h
section Tele
open Finset
open Classical
lemma red_syrZ (m j : ℕ) (w : Fin (m + j) → ℕ) :
    red m (m + j) (syrZ (m + j) (padv w)) = syrZ m (padv (lft w)) := by
  unfold red
  rw [← ZMod.cast_eq_val, ← ZMod.castHom_apply (h := pow_dvd_pow 3 (Nat.le_add_right m j)),
    syrZ_lr]
  unfold syrZ
  simp only [map_add, map_mul, map_pow, map_natCast, map_ofNat, castHom_two_inv_gen,
    three_pow_self_zmod, zero_mul, add_zero]


theorem proj_mu (m j K : ℕ) (Z : ZMod (3 ^ m)) :
    proj m (m + j) (mu (m + j) K) Z = mu m K Z * ∑ v ∈ Box j K, ((1 : ℝ) / 2) ^ (∑ i, v i) := by
  unfold proj mu
  calc ∑ Y ∈ univ.filter (fun Y => red m (m + j) Y = Z),
        ∑ w ∈ (Box (m + j) K).filter (fun w => syrZ (m + j) (padv w) = Y), ((1 : ℝ) / 2) ^ (∑ i, w i)
      = ∑ w ∈ (Box (m + j) K).filter (fun w => red m (m + j) (syrZ (m + j) (padv w)) = Z),
          ((1 : ℝ) / 2) ^ (∑ i, w i) := by
        rw [← Finset.sum_fiberwise_of_maps_to
          (s := (Box (m + j) K).filter (fun w => red m (m + j) (syrZ (m + j) (padv w)) = Z))
          (t := univ.filter (fun Y => red m (m + j) Y = Z)) (g := fun w => syrZ (m + j) (padv w))
          (by intro w hw; simp only [mem_filter, mem_univ, true_and] at hw ⊢; exact hw.2)]
        refine sum_congr rfl (fun Y hY => ?_)
        rw [filter_filter]
        refine sum_congr (filter_congr (fun w _ => ?_)) (fun _ _ => rfl)
        simp only [mem_filter, mem_univ, true_and] at hY
        constructor
        · intro hw; exact ⟨by rw [hw]; exact hY, hw⟩
        · rintro ⟨_, hw⟩; exact hw
    _ = _ := by
        rw [Finset.sum_mul_sum, ← Finset.sum_product']
        refine Finset.sum_nbij' (fun w => (lft w, rgt w)) (fun p => Fin.append p.1 p.2)
          ?_ ?_ ?_ ?_ ?_
        · intro w hw
          simp only [mem_filter, mem_product] at hw ⊢
          rw [mem_Box_iff, red_syrZ] at hw
          exact ⟨⟨hw.1.1, hw.2⟩, hw.1.2⟩
        · intro p hp
          simp only [mem_filter, mem_product] at hp ⊢
          rw [mem_Box_iff, red_syrZ, lft_append, rgt_append]
          exact ⟨⟨hp.1.1, hp.2⟩, hp.1.2⟩
        · intro w _; simp [append_lft_rgt]
        · intro p _; simp [lft_append, rgt_append]
        · intro w _; rw [sum_lft_rgt w, pow_add]


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
lemma sum_filter_or_le {α : Type*} (S : Finset α) (B₁ B₂ : α → Prop) [DecidablePred B₁]
    [DecidablePred B₂] (f : α → ℝ) (hf : ∀ a, 0 ≤ f a) :
    ∑ a ∈ S.filter (fun a => B₁ a ∨ B₂ a), f a ≤
      ∑ a ∈ S.filter B₁, f a + ∑ a ∈ S.filter B₂, f a := by
  simp only [Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum (fun a _ => ?_)
  have := hf a
  by_cases h1 : B₁ a <;> by_cases h2 : B₂ a <;> simp [h1, h2] <;> linarith


lemma sum_filter_exists_le {α : Type*} (S : Finset α) (J : Finset ℕ) (B : ℕ → α → Prop)
    (d1 : ∀ j, DecidablePred (B j)) (d2 : DecidablePred (fun a => ∃ j ∈ J, B j a))
    (f : α → ℝ) (hf : ∀ a, 0 ≤ f a) :
    ∑ a ∈ @Finset.filter α (fun a => ∃ j ∈ J, B j a) d2 S, f a ≤
      ∑ j ∈ J, ∑ a ∈ @Finset.filter α (B j) (d1 j) S, f a := by
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum (fun a _ => ?_)
  have hnn : ∀ j ∈ J, 0 ≤ (if B j a then f a else 0) := fun j _ => by
    split_ifs
    · exact hf a
    · exact le_refl 0
  split_ifs with h
  · obtain ⟨j, hj, hB⟩ := h
    have := Finset.single_le_sum (f := fun j => if B j a then f a else 0) hnn hj
    rw [if_pos hB] at this
    exact this
  · exact Finset.sum_nonneg hnn


/-- Prefix marginal: an event on `ps a j` has the same `Box`-mass in length `j + q` as in length `j`
(up to the factor `mass(Box q K) ≤ 1`). -/
lemma prefix_marg (j q K : ℕ) (R : ℕ → Prop) [DecidablePred R] :
    ∑ w ∈ (Box (j + q) K).filter (fun w => R (ps (padv w) j)), ((1 : ℝ) / 2) ^ (∑ i, w i) ≤
      ∑ u ∈ (Box j K).filter (fun u => R (∑ i, u i)), ((1 : ℝ) / 2) ^ (∑ i, u i) := by
  have hps : ∀ w : Fin (j + q) → ℕ, ps (padv w) j = ∑ i, lft w i := by
    intro w; rw [← ps_padv]; exact ps_congr _ _ _ (fun i hi => padv_lft w i hi)
  have heq : ∑ w ∈ (Box (j + q) K).filter (fun w => R (ps (padv w) j)),
      ((1 : ℝ) / 2) ^ (∑ i, w i) =
      (∑ u ∈ (Box j K).filter (fun u => R (∑ i, u i)), ((1 : ℝ) / 2) ^ (∑ i, u i)) *
        ∑ v ∈ Box q K, ((1 : ℝ) / 2) ^ (∑ i, v i) := by
    rw [Finset.sum_mul_sum, ← Finset.sum_product']
    refine Finset.sum_nbij' (fun w => (lft w, rgt w)) (fun p => Fin.append p.1 p.2)
      ?_ ?_ ?_ ?_ ?_
    · intro w hw
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hw ⊢
      rw [mem_Box_iff] at hw
      refine ⟨⟨hw.1.1, ?_⟩, hw.1.2⟩
      rw [← hps]; exact hw.2
    · intro p hp
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hp ⊢
      rw [mem_Box_iff, lft_append, rgt_append, hps, lft_append]
      exact ⟨⟨hp.1.1, hp.2⟩, hp.1.2⟩
    · intro w _; simp [append_lft_rgt]
    · intro p _; simp [lft_append, rgt_append]
    · intro w _
      dsimp only
      rw [sum_lft_rgt w, pow_add]
  rw [heq]
  calc _ ≤ (∑ u ∈ (Box j K).filter (fun u => R (∑ i, u i)), ((1 : ℝ) / 2) ^ (∑ i, u i)) * 1 :=
        mul_le_mul_of_nonneg_left (box_mass_le_syr q K)
          (Finset.sum_nonneg (fun _ _ => by positivity))
    _ = _ := mul_one _


lemma prefix_marg' (n K j : ℕ) (hj : j ≤ n) (R : ℕ → Prop) [DecidablePred R] :
    ∑ w ∈ (Box n K).filter (fun w => R (ps (padv w) j)), ((1 : ℝ) / 2) ^ (∑ i, w i) ≤
      ∑ u ∈ (Box j K).filter (fun u => R (∑ i, u i)), ((1 : ℝ) / 2) ^ (∑ i, u i) := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le hj
  exact prefix_marg j q K R


lemma exp_dev_le (j : ℕ) (hj : 1 ≤ j) (C L : ℝ) (hC : 1 ≤ C) (hL : 0 ≤ L) :
    Real.exp (-((C * (Real.sqrt (j * L) + L)) * min (C * (Real.sqrt (j * L) + L) / j) 1) / 24)
      ≤ Real.exp (-(C * L) / 24) := by
  apply Real.exp_le_exp.2
  set s := Real.sqrt (j * L) with hs_def
  set t := C * (s + L) with ht_def
  have hjR : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hC0 : (0 : ℝ) ≤ C := by linarith
  have ht : C * L ≤ t := by rw [ht_def]; nlinarith
  suffices h : C * L ≤ t * min (t / j) 1 by linarith
  rcases le_total (t / j) 1 with h | h
  · rw [min_eq_left h]
    have hsq : s ^ 2 = j * L := Real.sq_sqrt (by positivity)
    have h1 : C * s ≤ t := by rw [ht_def]; nlinarith
    have h2 : (C * s) ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
    have h3 : C * L * j ≤ (C * s) ^ 2 := by
      rw [mul_pow, hsq]
      have := mul_nonneg (mul_nonneg (mul_nonneg hC0 hL) (by linarith : (0 : ℝ) ≤ j))
        (sub_nonneg.2 hC)
      nlinarith
    rw [show t * (t / j) = t ^ 2 / j by ring, le_div_iff₀ (by linarith)]
    linarith
  · rw [min_eq_right h, mul_one]; exact ht


/-- Tao (6.3) (prefix form): `P(¬E) ≤ 2n e^{-CL/24}` via Lemma 2.2 and the union bound. -/
theorem dev_bad_mass (n K : ℕ) (C L : ℝ) (hC : 1 ≤ C) (hL : 0 ≤ L) :
    ∑ w ∈ (Box n K).filter (fun w => ¬ DevOK C L (padv w) n), ((1 : ℝ) / 2) ^ (∑ i, w i)
      ≤ 2 * n * Real.exp (-(C * L) / 24) := by
  have hf : ∀ w : Fin n → ℕ, (0 : ℝ) ≤ ((1 : ℝ) / 2) ^ (∑ i, w i) := fun _ => by positivity
  have hsub0 : (Box n K).filter (fun w => ¬ DevOK C L (padv w) n) ⊆
      (Box n K).filter (fun w => ∃ j ∈ Finset.Icc 1 n,
        C * (Real.sqrt (j * L) + L) < |(ps (padv w) j : ℝ) - 2 * j|) := by
    intro w hw
    simp only [Finset.mem_filter] at hw ⊢
    refine ⟨hw.1, ?_⟩
    have h2 := hw.2
    unfold DevOK at h2
    push_neg at h2
    exact h2
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub0 (fun w _ _ => hf w)) ?_
  set f : (Fin n → ℕ) → ℝ := fun w => ((1 : ℝ) / 2) ^ (∑ i, w i) with hf_def
  refine le_trans (sum_filter_exists_le (Box n K) (Finset.Icc 1 n)
    (fun j w => C * (Real.sqrt (j * L) + L) < |(ps (padv w) j : ℝ) - 2 * j|)
    (fun j => inferInstance) _ f hf) ?_
  have hj : ∀ j ∈ Finset.Icc 1 n,
      ∑ w ∈ (Box n K).filter (fun w =>
        C * (Real.sqrt (j * L) + L) < |(ps (padv w) j : ℝ) - 2 * j|), f w
        ≤ 2 * Real.exp (-(C * L) / 24) := by
    intro j hjm
    rw [Finset.mem_Icc] at hjm
    set t := C * (Real.sqrt (j * L) + L) with ht_def
    have ht0 : 0 ≤ t := by rw [ht_def]; have := Real.sqrt_nonneg (j * L); nlinarith
    have hsub : (Box n K).filter (fun w => t < |(ps (padv w) j : ℝ) - 2 * j|) ⊆
        (Box n K).filter (fun w => 2 * (j : ℝ) + t ≤ ((ps (padv w) j : ℕ) : ℝ) ∨
          ((ps (padv w) j : ℕ) : ℝ) ≤ 2 * (j : ℝ) - t) := by
      intro w hw
      simp only [Finset.mem_filter] at hw ⊢
      refine ⟨hw.1, ?_⟩
      rcases lt_abs.1 hw.2 with h | h
      · left; linarith
      · right; linarith
    have hsum : ∑ w ∈ (Box n K).filter (fun w => t < |(ps (padv w) j : ℝ) - 2 * j|), f w ≤
        ∑ w ∈ (Box n K).filter (fun w => 2 * (j : ℝ) + t ≤ ((ps (padv w) j : ℕ) : ℝ)), f w +
        ∑ w ∈ (Box n K).filter (fun w => ((ps (padv w) j : ℕ) : ℝ) ≤ 2 * (j : ℝ) - t), f w :=
      le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun w _ _ => hf w))
        (sum_filter_or_le (Box n K)
              (fun w => 2 * (j : ℝ) + t ≤ ((ps (padv w) j : ℕ) : ℝ))
              (fun w => ((ps (padv w) j : ℕ) : ℝ) ≤ 2 * (j : ℝ) - t) f hf)
    have hu : ∑ w ∈ (Box n K).filter (fun w => 2 * (j : ℝ) + t ≤ ((ps (padv w) j : ℕ) : ℝ)),
        f w ≤ Real.exp (-(t * min (t / j) 1) / 24) := by
      exact le_trans (prefix_marg' n K j hjm.2 (fun s => 2 * (j : ℝ) + t ≤ ((s : ℕ) : ℝ)))
        (chernoff_up j K hjm.1 t ht0)
    have hd : ∑ w ∈ (Box n K).filter (fun w => ((ps (padv w) j : ℕ) : ℝ) ≤ 2 * (j : ℝ) - t),
        f w ≤ Real.exp (-(t * min (t / j) 1) / 24) := by
      exact le_trans (prefix_marg' n K j hjm.2 (fun s => ((s : ℕ) : ℝ) ≤ 2 * (j : ℝ) - t))
        (chernoff_down j K hjm.1 t ht0)
    have he := exp_dev_le j hjm.1 C L hC hL
    rw [← ht_def] at he
    linarith
  refine le_trans (Finset.sum_le_sum hj) ?_
  rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
  simp only [Nat.add_sub_cancel]
  linarith


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

end IF114
section IF111
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

end IF111
section C4
open Classical
end C4
end Tao31

open Tao31 in
theorem solution :
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
          μ₁ Z * ∑ v ∈ Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 K), ((1 : ℝ) / 2) ^ (∑ i, v i)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro P hP y n hn hM hZ E _
    have hPp : P = prob := funext fun y => funext fun Q => (hP y Q).trans (prob_ProbEq y Q).symm
    subst hPp
    have h := prop19_Ny y n hn hM hZ E
    convert h
    all_goals first | rfl | (intros; rfl)
  · intro n K hn
    exact box_tail19 n K hn
  · intro n K C L hC hL
    have h := dev_bad_mass n K C L hC hL
    rw [Finset.sum_filter] at h
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
  · intro m j K μ₁ μ₂ h₁ h₂ Z
    have e₁ : μ₁ = mu m K := funext fun Y => (h₁ Y).trans (mu_MuEq m K Y).symm
    have e₂ : μ₂ = mu (m + j) K := funext fun Y => (h₂ Y).trans (mu_MuEq (m + j) K Y).symm
    subst e₁ e₂
    exact proj_mu m j K Z
