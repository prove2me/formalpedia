-- Prove2me | solution 1 for PiIrrationality.ZZEven.phi_lower
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-05T09:47:48.093353+00:00
-- url     : https://prove2.me/submissions/ed9685fb-8377-48f6-9772-d59abc383e03

import Definitions.Def_PiIrrationality_ZZEvenForms
import Theorems.Thm_MediumPNT
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.NumberTheory.Chebyshev

open Filter Real Asymptotics
open scoped Topology

namespace PiIrrationality.ZZEven.PhiLower

/-- `|ψ x - x| ≤ ε x` eventually (prime number theorem). -/
lemma psi_near (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, |Chebyshev.psi x - x| ≤ ε * x := by
  obtain ⟨c, hc, hO⟩ := MediumPNT
  obtain ⟨C, hC, hbound⟩ := hO.exists_pos
  have ht : Tendsto (fun x : ℝ => Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10)))
      atTop (𝓝 0) := by
    apply Real.tendsto_exp_atBot.comp
    have hh := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 10)).comp
      Real.tendsto_log_atTop
    simpa only [neg_mul, Function.comp_def] using
      tendsto_neg_atTop_atBot.comp (hh.const_mul_atTop hc)
  have he : ∀ᶠ x : ℝ in atTop,
      C * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10)) < ε :=
    (show Tendsto (fun x : ℝ => C * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10)))
      atTop (𝓝 0) by simpa using ht.const_mul C).eventually_lt_const hε
  filter_upwards [hbound.bound, he, eventually_ge_atTop (0 : ℝ)] with x hx he hx0
  have hxp := Real.exp_pos (-c * (Real.log x) ^ ((1 : ℝ) / 10))
  simp only [Pi.sub_apply, id_eq, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg hx0 hxp.le)] at hx
  calc |Chebyshev.psi x - x| ≤ C * (x * Real.exp (-c * Real.log x ^ ((1 : ℝ) / 10))) := hx
    _ = (C * Real.exp (-c * Real.log x ^ ((1 : ℝ) / 10))) * x := by ring
    _ ≤ ε * x := mul_le_mul_of_nonneg_right he.le hx0

/-- `2 √x log x ≤ ε x` eventually. -/
lemma sqrt_log_small (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, 2 * √x * Real.log x ≤ ε * x := by
  have h := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).bound
    (by positivity : (0 : ℝ) < ε / 2)
  filter_upwards [h, eventually_ge_atTop (1 : ℝ)] with x hx hx1
  have hx0 : (0 : ℝ) ≤ x := by linarith
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx1
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hlog,
    abs_of_nonneg (Real.rpow_nonneg hx0 _), ← Real.sqrt_eq_rpow] at hx
  have hs : √x * √x = x := Real.mul_self_sqrt hx0
  have hsq : 0 ≤ √x := Real.sqrt_nonneg x
  nlinarith

/-- `θ(x) = x + o(x)`. -/
lemma theta_near (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop,
      (1 - ε) * x ≤ Chebyshev.theta x ∧ Chebyshev.theta x ≤ (1 + ε) * x := by
  filter_upwards [psi_near (ε / 2) (by positivity), sqrt_log_small (ε / 2) (by positivity),
    eventually_ge_atTop (1 : ℝ)] with x hpsi hsl hx1
  have h1 := Chebyshev.theta_le_psi x
  have h2 := Chebyshev.psi_sub_theta_le hx1
  have h3 := abs_le.mp hpsi
  constructor <;> nlinarith [h3.1, h3.2]

/-- The difference of `θ` at two integers is the prime sum over the interval. -/
lemma theta_sub (A B : ℕ) (h : A ≤ B) :
    Chebyshev.theta B - Chebyshev.theta A =
      ∑ p ∈ (Finset.Ioc A B).filter Nat.Prime, Real.log p := by
  simp only [Chebyshev.theta, Nat.floor_natCast]
  rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter,
    ← Finset.sum_Ioc_consecutive _ (Nat.zero_le A) h]
  ring

/-- The primes of the `k`-th interval `(6n/(3k+2), 4n/(2k+1)]`. -/
noncomputable def S (k n : ℕ) : Finset ℕ :=
  (Finset.Ioc ⌊(6 * n : ℝ) / (3 * k + 2)⌋₊ ⌊(4 * n : ℝ) / (2 * k + 1)⌋₊).filter Nat.Prime

lemma floor_le_floor (k n : ℕ) :
    ⌊(6 * n : ℝ) / (3 * k + 2)⌋₊ ≤ ⌊(4 * n : ℝ) / (2 * k + 1)⌋₊ := by
  apply Nat.floor_le_floor
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n), (Nat.cast_nonneg k : (0 : ℝ) ≤ k)]

lemma S_sum (k n : ℕ) :
    ∑ p ∈ S k n, Real.log p =
      Chebyshev.theta ((4 * n : ℝ) / (2 * k + 1)) - Chebyshev.theta ((6 * n : ℝ) / (3 * k + 2)) := by
  rw [Chebyshev.theta_eq_theta_coe_floor ((4 * n : ℝ) / (2 * k + 1)),
    Chebyshev.theta_eq_theta_coe_floor ((6 * n : ℝ) / (3 * k + 2)),
    theta_sub _ _ (floor_le_floor k n)]
  rfl

/-- Membership in `S k n` in terms of natural-number inequalities. -/
lemma mem_S {k n p : ℕ} (hp : p ∈ S k n) :
    p.Prime ∧ 6 * n < (3 * k + 2) * p ∧ (2 * k + 1) * p ≤ 4 * n := by
  unfold S at hp
  rw [Finset.mem_filter, Finset.mem_Ioc] at hp
  obtain ⟨⟨h1, h2⟩, hpr⟩ := hp
  refine ⟨hpr, ?_, ?_⟩
  · have := (Nat.floor_lt (by positivity)).mp h1
    rw [div_lt_iff₀ (by positivity)] at this
    exact_mod_cast (show ((6 * n : ℕ) : ℝ) < ((3 * k + 2) * p : ℕ) by push_cast; linarith)
  · have := (Nat.le_floor_iff (by positivity)).mp h2
    rw [le_div_iff₀ (by positivity)] at this
    exact_mod_cast (show (((2 * k + 1) * p : ℕ) : ℝ) ≤ ((4 * n : ℕ) : ℝ) by push_cast; linarith)

lemma fract_eq (r : ℚ) (m : ℤ) (h1 : (m : ℚ) ≤ r) (h2 : r < m + 1) : Int.fract r = r - m := by
  rw [Int.fract, (Int.floor_eq_iff.mpr ⟨h1, h2⟩)]

/-- Every prime of `S k n` is a deleted prime once `n ≥ 5 (3k+2)^2`. -/
lemma S_subset (k n : ℕ) (hn : 5 * (3 * k + 2) ^ 2 ≤ n) : S k n ⊆ deletedPrimes n := by
  intro p hp
  obtain ⟨hpr, hlo, hhi⟩ := mem_S hp
  have hp0 : 0 < p := hpr.pos
  unfold deletedPrimes
  rw [Finset.mem_filter, Finset.mem_range]
  have hk2 : 2 ≤ 3 * k + 2 := by omega
  refine ⟨?_, hpr, ?_, ?_, ?_⟩
  · nlinarith
  · -- 5 < p
    by_contra h
    push Not at h
    have : (3 * k + 2) * p ≤ (3 * k + 2) * 5 := Nat.mul_le_mul_left _ h
    nlinarith
  · -- 8n < p^2
    have hn0 : 0 < n := by nlinarith
    have h36 : 36 * n ^ 2 < ((3 * k + 2) * p) ^ 2 := by nlinarith
    have h5 : 36 * n * (5 * (3 * k + 2) ^ 2) ≤ 36 * n * n := Nat.mul_le_mul_left _ hn
    have hq : 0 < (3 * k + 2) ^ 2 := by positivity
    have : 8 * n * (3 * k + 2) ^ 2 < 36 * n ^ 2 := by nlinarith
    have h' : (3 * k + 2) ^ 2 * (8 * n) < (3 * k + 2) ^ 2 * p ^ 2 := by
      have := lt_trans this h36
      rw [mul_pow] at this
      linarith
    exact Nat.lt_of_mul_lt_mul_left h'
  · -- the fractional-part inequality
    have hpq : (0 : ℚ) < p := by exact_mod_cast hp0
    set x : ℚ := (2 * n : ℚ) / p with hx
    have hlo' : (6 * n : ℚ) < (3 * k + 2) * p := by exact_mod_cast hlo
    have hhi' : (2 * k + 1 : ℚ) * p ≤ 4 * n := by exact_mod_cast hhi
    have hxlo : (k : ℚ) + 1 / 2 ≤ x := by
      rw [hx, le_div_iff₀ hpq]; linarith
    have hxhi : x < (k : ℚ) + 2 / 3 := by
      rw [hx, div_lt_iff₀ hpq]; linarith
    have e4 : (4 * n : ℚ) / p = 2 * x := by rw [hx]; ring
    have e6 : (6 * n : ℚ) / p = 3 * x := by rw [hx]; ring
    have f1 : Int.fract (x + 1 / 2) = x + 1 / 2 - ((k + 1 : ℤ) : ℚ) :=
      fract_eq _ _ (by push_cast; linarith) (by push_cast; linarith)
    have f2 : Int.fract (2 * x) = 2 * x - ((2 * k + 1 : ℤ) : ℚ) :=
      fract_eq _ _ (by push_cast; linarith) (by push_cast; linarith)
    have f3 : Int.fract (3 * x) = 3 * x - ((3 * k + 1 : ℤ) : ℚ) :=
      fract_eq _ _ (by push_cast; linarith) (by push_cast; linarith)
    rw [e4, e6, f1, f2, f3]
    push_cast
    linarith

lemma S_disjoint (n : ℕ) {k k' : ℕ} (hkk : k ≠ k') : Disjoint (S k n) (S k' n) := by
  rw [Finset.disjoint_left]
  intro p hp hp'
  obtain ⟨hpr, h1, h2⟩ := mem_S hp
  obtain ⟨_, h1', h2'⟩ := mem_S hp'
  apply hkk
  -- 2k+1 ≤ 4n/p < 2k + 4/3 determines k
  rcases lt_trichotomy k k' with h | h | h
  · exfalso
    have : (2 * k + 3) * p ≤ (2 * k' + 1) * p := Nat.mul_le_mul_right _ (by omega)
    nlinarith
  · exact h
  · exfalso
    have : (2 * k' + 3) * p ≤ (2 * k + 1) * p := Nat.mul_le_mul_right _ (by omega)
    nlinarith

end PiIrrationality.ZZEven.PhiLower

open PiIrrationality.ZZEven PiIrrationality.ZZEven.PhiLower in
theorem solution (K : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in Filter.atTop,
      Real.exp (((∑ k ∈ Finset.range K,
          ((4 : ℝ) / (2 * k + 1) - 6 / (3 * k + 2))) - δ) * (n : ℝ)) ≤
        (PiIrrationality.ZZEven.Phi n : ℝ) := by
  set ε : ℝ := δ / (7 * K + 1) with hε
  have hε0 : 0 < ε := by positivity
  -- θ estimates at both ends of every interval
  have hθ : ∀ k ∈ Finset.range K, ∀ᶠ n : ℕ in atTop,
      (1 - ε) * ((4 * n : ℝ) / (2 * k + 1)) ≤ Chebyshev.theta ((4 * n : ℝ) / (2 * k + 1)) ∧
      Chebyshev.theta ((6 * n : ℝ) / (3 * k + 2)) ≤ (1 + ε) * ((6 * n : ℝ) / (3 * k + 2)) := by
    intro k _
    have hb : Tendsto (fun n : ℕ => (4 * n : ℝ) / (2 * k + 1)) atTop atTop := by
      have : Tendsto (fun n : ℕ => (n : ℝ) * (4 / (2 * k + 1))) atTop atTop :=
        tendsto_natCast_atTop_atTop.atTop_mul_const (by positivity)
      refine this.congr fun n => by ring
    have ha : Tendsto (fun n : ℕ => (6 * n : ℝ) / (3 * k + 2)) atTop atTop := by
      have : Tendsto (fun n : ℕ => (n : ℝ) * (6 / (3 * k + 2))) atTop atTop :=
        tendsto_natCast_atTop_atTop.atTop_mul_const (by positivity)
      refine this.congr fun n => by ring
    filter_upwards [hb.eventually (theta_near ε hε0), ha.eventually (theta_near ε hε0)]
      with n h1 h2
    exact ⟨h1.1, h2.2⟩
  have hall := (Finset.range K).eventually_all.mpr hθ
  filter_upwards [hall, eventually_ge_atTop (5 * (3 * K + 2) ^ 2)] with n hn hnK
  have hPhi : 0 < (Phi n : ℝ) := by
    unfold Phi
    exact_mod_cast Finset.prod_pos fun p hp => by
      unfold deletedPrimes at hp
      exact (Finset.mem_filter.mp hp).2.1.pos
  rw [← Real.exp_log hPhi, Real.exp_le_exp]
  -- log Φ_n ≥ Σ_k Σ_{S k n} log p
  have hlogPhi : Real.log (Phi n : ℝ) = ∑ p ∈ deletedPrimes n, Real.log p := by
    unfold Phi
    push_cast
    rw [Real.log_prod]
    intro p hp
    unfold deletedPrimes at hp
    exact_mod_cast (Finset.mem_filter.mp hp).2.1.ne_zero
  have hsub : (Finset.range K).biUnion (fun k => S k n) ⊆ deletedPrimes n := by
    intro p hp
    rw [Finset.mem_biUnion] at hp
    obtain ⟨k, hk, hpk⟩ := hp
    have hkK : k < K := Finset.mem_range.mp hk
    exact S_subset k n (le_trans (Nat.mul_le_mul_left 5 (Nat.pow_le_pow_left (by omega) 2))
      hnK) hpk
  have hdisj : Set.PairwiseDisjoint (↑(Finset.range K)) (fun k => S k n) :=
    fun k _ k' _ hkk => S_disjoint n hkk
  have h1 : ∑ k ∈ Finset.range K, ∑ p ∈ S k n, Real.log p ≤ Real.log (Phi n : ℝ) := by
    rw [hlogPhi, ← Finset.sum_biUnion hdisj]
    apply Finset.sum_le_sum_of_subset_of_nonneg hsub
    intro p _ _
    exact Real.log_natCast_nonneg p
  refine le_trans ?_ h1
  -- each interval contributes at least (b - a - ε (a + b)) n
  have h2 : ∀ k ∈ Finset.range K,
      ((4 : ℝ) / (2 * k + 1) - 6 / (3 * k + 2) - 7 * ε) * n ≤ ∑ p ∈ S k n, Real.log p := by
    intro k hk
    rw [S_sum]
    obtain ⟨hb, ha⟩ := hn k hk
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hab : (4 : ℝ) / (2 * k + 1) + 6 / (3 * k + 2) ≤ 7 := by
      have e1 : (4 : ℝ) / (2 * k + 1) ≤ 4 := div_le_self (by norm_num) (by linarith)
      have e2 : (6 : ℝ) / (3 * k + 2) ≤ 3 := by
        rw [div_le_iff₀ (by positivity)]; linarith
      linarith
    have eb : (4 * n : ℝ) / (2 * k + 1) = 4 / (2 * k + 1) * n := by ring
    have ea : (6 * n : ℝ) / (3 * k + 2) = 6 / (3 * k + 2) * n := by ring
    rw [eb] at hb ⊢; rw [ea] at ha ⊢
    have hpos1 : 0 ≤ (4 : ℝ) / (2 * k + 1) * n := by positivity
    have hpos2 : 0 ≤ (6 : ℝ) / (3 * k + 2) * n := by positivity
    nlinarith [mul_le_mul_of_nonneg_right hab hn0, hε0]
  have hKε : (K : ℝ) * (7 * ε) ≤ δ := by
    have h7 : (0 : ℝ) < 7 * K + 1 := by positivity
    have : (K : ℝ) * (7 * ε) * (7 * K + 1) = 7 * K * δ := by rw [hε]; field_simp
    nlinarith
  calc ((∑ k ∈ Finset.range K, ((4 : ℝ) / (2 * k + 1) - 6 / (3 * k + 2))) - δ) * n
      ≤ ((∑ k ∈ Finset.range K, ((4 : ℝ) / (2 * k + 1) - 6 / (3 * k + 2))) -
          (K : ℝ) * (7 * ε)) * n :=
        mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg n)
    _ = ∑ k ∈ Finset.range K, ((4 : ℝ) / (2 * k + 1) - 6 / (3 * k + 2) - 7 * ε) * n := by
        simp only [sub_mul, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
          nsmul_eq_mul, Finset.sum_mul]
        ring
    _ ≤ ∑ k ∈ Finset.range K, ∑ p ∈ S k n, Real.log p := Finset.sum_le_sum h2
