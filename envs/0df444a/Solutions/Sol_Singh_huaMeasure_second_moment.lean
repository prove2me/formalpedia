-- Prove2me | solution 1 for Singh.huaMeasure_second_moment
-- status  : ACCEPTED   (prove)
-- author  : @Hix_Lab
-- created : 2026-11-04T06:06:26.201676+00:00
-- url     : https://prove2.me/submissions/a20f277f-11da-44ab-8afa-c8ce2a70b033

import Mathlib
import Definitions.Def_Singh




/-!
# Singh Theorem: algebraic core

Pointwise loop-equation identities for the Hua (Cauchy) ensemble
`P_{n,h}(u) ∝ ∏ (1+u_k^2)^{-(n+h)} ∏_{j<k} (u_j-u_k)^2`,
the solution of the two loop equations, and the closed form
`c_N = (π^2/15)(1 - 4/N^2)`.
-/

open Finset BigOperators

namespace Singh

variable {n : ℕ}

/-- Antisymmetrization: for distinct points,
`∑_{k≠j} a_k/(u_k-u_j) = (1/2) ∑_{k≠j} (a_k-a_j)/(u_k-u_j)`. -/
theorem pair_sum_symm (u a : Fin n → ℝ) :
    ∑ k, ∑ j ∈ univ.erase k, a k / (u k - u j)
      = (1/2) * ∑ k, ∑ j ∈ univ.erase k, (a k - a j) / (u k - u j) := by
  have hswap : ∑ k, ∑ j ∈ univ.erase k, a k / (u k - u j)
      = ∑ k, ∑ j ∈ univ.erase k, (- a j) / (u k - u j) := by
    have h1 : ∀ f : Fin n → Fin n → ℝ,
        ∑ k, ∑ j ∈ univ.erase k, f k j = ∑ k, ∑ j ∈ univ.erase k, f j k := by
      intro f
      simp only [sum_erase_eq_sub (mem_univ _)]
      rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_comm]
    rw [h1]
    refine sum_congr rfl fun k _ => sum_congr rfl fun j _ => ?_
    rw [show u j - u k = -(u k - u j) by ring, div_neg, neg_div]
  have : ∑ k, ∑ j ∈ univ.erase k, (a k - a j) / (u k - u j)
      = ∑ k, ∑ j ∈ univ.erase k, a k / (u k - u j)
        + ∑ k, ∑ j ∈ univ.erase k, (- a j) / (u k - u j) := by
    rw [← sum_add_distrib]
    refine sum_congr rfl fun k _ => ?_
    rw [← sum_add_distrib]
    refine sum_congr rfl fun j _ => ?_
    ring
  rw [this, ← hswap]; ring

/-- Sum over ordered pairs `k ≠ j` of a constant. -/
theorem sum_offdiag_const (c : ℝ) :
    ∑ k : Fin n, ∑ _j ∈ univ.erase k, c = (n : ℝ) * (n - 1) * c := by
  simp only [sum_const, card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  rcases n with _ | m
  · simp
  · push_cast; ring

/-- `∑_{k≠j} (u_k + u_j) = 2(n-1) ∑ u`. -/
theorem sum_offdiag_add (u : Fin n → ℝ) :
    ∑ k, ∑ j ∈ univ.erase k, (u k + u j) = 2 * ((n : ℝ) - 1) * ∑ k, u k := by
  have e : ∀ k, ∑ j ∈ univ.erase k, (u k + u j)
      = ((n : ℝ) - 1) * u k + (∑ j, u j - u k) := by
    intro k
    rw [sum_add_distrib, sum_const, card_erase_of_mem (mem_univ _), card_univ,
      Fintype.card_fin, nsmul_eq_mul, sum_erase_eq_sub (mem_univ _)]
    rcases n with _ | m
    · exact (Fin.elim0 k)
    · push_cast; ring
  simp only [e, sum_add_distrib, sum_sub_distrib, sum_const, card_univ, Fintype.card_fin,
    nsmul_eq_mul, ← mul_sum]
  ring

/-- `∑_k u_k ∑_{j≠k} u_j = (∑ u)^2 - ∑ u^2`. -/
theorem sum_offdiag_mul (u : Fin n → ℝ) :
    ∑ k, u k * ∑ j ∈ univ.erase k, u j = (∑ k, u k) ^ 2 - ∑ k, u k ^ 2 := by
  have e : ∀ k, u k * ∑ j ∈ univ.erase k, u j = u k * ∑ j, u j - u k ^ 2 := by
    intro k
    rw [sum_erase_eq_sub (mem_univ _)]; ring
  simp only [e, sum_sub_distrib, ← sum_mul]
  ring

/-- `∑_{k≠j} (u_k^2 + u_j^2) = 2(n-1) ∑ u^2`. -/
theorem sum_offdiag_sq (u : Fin n → ℝ) :
    ∑ k, ∑ j ∈ univ.erase k, (u k ^ 2 + u j ^ 2) = 2 * ((n : ℝ) - 1) * ∑ k, u k ^ 2 :=
  sum_offdiag_add (fun k => u k ^ 2)

/-- Additivity of off-diagonal sums. -/
theorem sum_offdiag_add3 (f g e : Fin n → Fin n → ℝ) :
    ∑ k, ∑ j ∈ univ.erase k, (f k j + (g k j + e k j))
      = ∑ k, ∑ j ∈ univ.erase k, f k j + (∑ k, ∑ j ∈ univ.erase k, g k j
        + ∑ k, ∑ j ∈ univ.erase k, e k j) := by
  simp only [sum_add_distrib]

/-- First pair identity: `∑_{k≠j} 2(1+u_k^2)/(u_k-u_j) = 2(n-1) ∑ u_k`. -/
theorem pair_identity_a (u : Fin n → ℝ) (hu : Function.Injective u) :
    ∑ k, ∑ j ∈ univ.erase k, 2 * (1 + u k ^ 2) / (u k - u j)
      = 2 * ((n : ℝ) - 1) * ∑ k, u k := by
  rw [pair_sum_symm]
  have : ∀ k, ∀ j ∈ univ.erase k,
      (2 * (1 + u k ^ 2) - 2 * (1 + u j ^ 2)) / (u k - u j) = 2 * (u k + u j) := by
    intro k j hj
    have hne : u k - u j ≠ 0 := sub_ne_zero.mpr (hu.ne (ne_of_mem_erase hj).symm)
    field_simp; ring
  rw [sum_congr rfl fun k _ => sum_congr rfl (this k)]
  simp only [← mul_sum]
  rw [sum_offdiag_add]; ring

/-- Second pair identity:
`∑_{k≠j} 2u_k(1+u_k^2)/(u_k-u_j) = n(n-1) + 2(n-1)∑u^2 + (∑u)^2 - ∑u^2`. -/
theorem pair_identity_b (u : Fin n → ℝ) (hu : Function.Injective u) :
    ∑ k, ∑ j ∈ univ.erase k, 2 * (u k * (1 + u k ^ 2)) / (u k - u j)
      = (n : ℝ) * (n - 1) + 2 * ((n : ℝ) - 1) * ∑ k, u k ^ 2
        + (∑ k, u k) ^ 2 - ∑ k, u k ^ 2 := by
  rw [pair_sum_symm]
  have : ∀ k, ∀ j ∈ univ.erase k,
      (2 * (u k * (1 + u k ^ 2)) - 2 * (u j * (1 + u j ^ 2))) / (u k - u j)
        = 2 * 1 + (2 * (u k ^ 2 + u j ^ 2) + 2 * (u k * u j)) := by
    intro k j hj
    have hne : u k - u j ≠ 0 := sub_ne_zero.mpr (hu.ne (ne_of_mem_erase hj).symm)
    field_simp; ring
  rw [sum_congr rfl fun k _ => sum_congr rfl (this k)]
  have e := sum_offdiag_add3 (fun _ _ => 2 * (1 : ℝ)) (fun k j => 2 * (u k ^ 2 + u j ^ 2))
    (fun k j => 2 * (u k * u j))
  rw [e]
  simp only [← mul_sum]
  rw [sum_offdiag_const, sum_offdiag_sq, sum_offdiag_mul]; ring

/-- Logarithmic derivative of the Hua density in the variable `u_k`. -/
noncomputable def logDeriv (h : ℝ) (u : Fin n → ℝ) (k : Fin n) : ℝ :=
  -(2 * ((n : ℝ) + h) * u k) / (1 + u k ^ 2) + ∑ j ∈ univ.erase k, 2 / (u k - u j)

/-- Divergence integrand for loop equation (a):
`∑_k P^{-1} ∂_k[(1+u_k^2) F P]` with `F = ∑ u`. -/
noncomputable def divA (h : ℝ) (u : Fin n → ℝ) : ℝ :=
  ∑ k, (2 * u k * (∑ j, u j) + (1 + u k ^ 2)
        + (1 + u k ^ 2) * (∑ j, u j) * logDeriv h u k)

/-- Divergence integrand for loop equation (b):
`∑_k P^{-1} ∂_k[(1+u_k^2) u_k P]`. -/
noncomputable def divB (h : ℝ) (u : Fin n → ℝ) : ℝ :=
  ∑ k, ((1 + 3 * u k ^ 2) + (1 + u k ^ 2) * u k * logDeriv h u k)

private lemma pos_sq (x : ℝ) : 1 + x ^ 2 ≠ 0 := by positivity

/-- Pointwise form of loop equation (a). -/
theorem divA_eq (h : ℝ) (u : Fin n → ℝ) (hu : Function.Injective u) :
    divA h u = (n : ℝ) + ∑ k, u k ^ 2 - 2 * h * (∑ k, u k) ^ 2 := by
  have hk : ∀ k, (1 + u k ^ 2) * logDeriv h u k
      = -(2 * ((n : ℝ) + h) * u k)
        + ∑ j ∈ univ.erase k, 2 * (1 + u k ^ 2) / (u k - u j) := by
    intro k
    unfold logDeriv
    rw [mul_add, mul_sum]
    congr 1
    · field_simp [pos_sq (u k)]
    · exact sum_congr rfl fun j _ => by ring
  unfold divA
  have : ∀ k, 2 * u k * (∑ j, u j) + (1 + u k ^ 2)
        + (1 + u k ^ 2) * (∑ j, u j) * logDeriv h u k
      = 2 * u k * (∑ j, u j) + (1 + u k ^ 2)
        + (∑ j, u j) * (-(2 * ((n : ℝ) + h) * u k))
        + (∑ j, u j) * ∑ j ∈ univ.erase k, 2 * (1 + u k ^ 2) / (u k - u j) := by
    intro k
    rw [show (1 + u k ^ 2) * (∑ j, u j) * logDeriv h u k
        = (∑ j, u j) * ((1 + u k ^ 2) * logDeriv h u k) by ring, hk]; ring
  rw [sum_congr rfl fun k _ => this k]
  simp only [sum_add_distrib, ← mul_sum, ← sum_mul, sum_neg_distrib]
  rw [pair_identity_a u hu]
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  ring

/-- Pointwise form of loop equation (b). -/
theorem divB_eq (h : ℝ) (u : Fin n → ℝ) (hu : Function.Injective u) :
    divB h u = (n : ℝ) ^ 2 - 2 * h * ∑ k, u k ^ 2 + (∑ k, u k) ^ 2 := by
  have hk : ∀ k, (1 + u k ^ 2) * u k * logDeriv h u k
      = -(2 * ((n : ℝ) + h) * u k ^ 2)
        + ∑ j ∈ univ.erase k, 2 * (u k * (1 + u k ^ 2)) / (u k - u j) := by
    intro k
    unfold logDeriv
    rw [mul_add, mul_sum]
    congr 1
    · field_simp [pos_sq (u k)]
    · exact sum_congr rfl fun j _ => by ring
  unfold divB
  rw [sum_congr rfl fun k _ => by rw [hk k]]
  simp only [sum_add_distrib, ← mul_sum, sum_neg_distrib]
  rw [pair_identity_b u hu]
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  ring

/-- Solution of the two loop equations. If `n + Q = 2h M` and
`n^2 - 2h Q + M = 0` with `4h^2 ≠ 1`, then `M = n(n+2h)/(4h^2-1)`. -/
theorem loop_solution (n h M Q : ℝ) (hh : 4 * h ^ 2 - 1 ≠ 0)
    (ha : n + Q = 2 * h * M) (hb : n ^ 2 - 2 * h * Q + M = 0) :
    M = n * (n + 2 * h) / (4 * h ^ 2 - 1) := by
  rw [eq_div_iff hh]
  have hQ : Q = 2 * h * M - n := by linarith
  subst hQ
  linear_combination -hb

/-- At `h = 2` and `n = N - 2`: `E[S^2] = M/4 = (N^2-4)/60`. -/
theorem moment_h2 (N : ℝ) :
    (N - 2) * ((N - 2) + 2 * 2) / (4 * 2 ^ 2 - 1) / 4 = (N ^ 2 - 4) / 60 := by
  ring

/-- Closed form of the constant: `(2π/N)^2 (N^2-4)/60 = (π^2/15)(1-4/N^2)`. -/
theorem cN_closed_form (N : ℝ) (hN : N ≠ 0) :
    (2 * Real.pi / N) ^ 2 * ((N ^ 2 - 4) / 60) = Real.pi ^ 2 / 15 * (1 - 4 / N ^ 2) := by
  field_simp; ring

/-- The Singh constant. -/
noncomputable def cN (N : ℕ) : ℝ := Real.pi ^ 2 / 15 * (1 - 4 / (N : ℝ) ^ 2)

/-- `c_N → π^2/15` as `N → ∞`. -/
theorem cN_tendsto :
    Filter.Tendsto cN Filter.atTop (nhds (Real.pi ^ 2 / 15)) := by
  have h : Filter.Tendsto (fun N : ℕ => (4 : ℝ) / (N : ℝ) ^ 2) Filter.atTop (nhds 0) := by
    have h2 : Filter.Tendsto (fun N : ℕ => (N : ℝ) ^ 2) Filter.atTop Filter.atTop :=
      (Filter.tendsto_pow_atTop two_ne_zero).comp tendsto_natCast_atTop_atTop
    exact Filter.Tendsto.div_atTop tendsto_const_nhds h2
  have := (tendsto_const_nhds (x := (1 : ℝ))).sub h
  unfold cN
  simpa using (tendsto_const_nhds (x := Real.pi ^ 2 / 15)).mul this

end Singh




/-!
# The Hua ensemble `P_{n,2}`

`P_{n,2}(u) = Z⁻¹ ∏_{j<k} (u_j-u_k)^2 ∏_k (1+u_k^2)^{-(n+2)}` on `ℝ^n`, written with
`∏_{j<k}(u_j-u_k)^2 = ∏_k ∏_{j≠k} |u_k-u_j|`.
We prove that it is a probability measure, that it is absolutely continuous
(so `u` has distinct coordinates almost surely), and that `(∑u)^2` and `∑u^2`
are integrable.
-/

open MeasureTheory Finset
open scoped ENNReal NNReal

namespace Singh

variable {n : ℕ}

lemma one_le_g (x : ℝ) : 1 ≤ 1 + x ^ 2 := by nlinarith [sq_nonneg x]

lemma one_le_bigG (u : Fin n → ℝ) : 1 ≤ bigG u := by
  unfold bigG
  calc (1 : ℝ) = ∏ _k : Fin n, (1 : ℝ) := by simp
    _ ≤ _ := Finset.prod_le_prod (fun _ _ => zero_le_one) (fun k _ => one_le_g (u k))

lemma bigG_pos (u : Fin n → ℝ) : 0 < bigG u := lt_of_lt_of_le one_pos (one_le_bigG u)

lemma vdm_nonneg (u : Fin n → ℝ) : 0 ≤ vdm u :=
  prod_nonneg fun _ _ => prod_nonneg fun _ _ => abs_nonneg _

lemma huaWeight_nonneg (u : Fin n → ℝ) : 0 ≤ huaWeight u :=
  div_nonneg (vdm_nonneg u) (pow_nonneg (bigG_pos u).le _)

lemma pair_bound (a b : ℝ) : (a - b) ^ 2 ≤ 2 * ((1 + a ^ 2) * (1 + b ^ 2)) := by
  nlinarith [sq_nonneg (a + b), sq_nonneg (a * b)]

lemma prod_erase_prod (g : Fin n → ℝ) (hg : ∀ k, 0 < g k) :
    ∏ k, ∏ j ∈ univ.erase k, g j = (∏ k, g k) ^ n / ∏ k, g k := by
  have e : ∀ k, ∏ j ∈ univ.erase k, g j = (∏ j, g j) / g k := fun k => by
    rw [eq_div_iff (hg k).ne', mul_comm, mul_prod_erase _ _ (mem_univ k)]
  simp only [e, prod_div_distrib, prod_const, card_univ, Fintype.card_fin]

lemma vdm_sq_le (u : Fin n → ℝ) :
    vdm u ^ 2 ≤ ((2 : ℝ) ^ n) ^ n * bigG u ^ (2 * n) := by
  have hg : ∀ k, 0 < 1 + u k ^ 2 := fun k => by positivity
  have hG := bigG_pos u
  have e1 : vdm u ^ 2 = ∏ k, ∏ j ∈ univ.erase k, (u k - u j) ^ 2 := by
    unfold vdm; rw [← prod_pow]; simp only [← prod_pow, sq_abs]
  have e2 : ∏ k, ∏ j ∈ univ.erase k, (u k - u j) ^ 2
      ≤ ∏ k, ∏ j ∈ univ.erase k, (2 * ((1 + u k ^ 2) * (1 + u j ^ 2))) :=
    Finset.prod_le_prod (fun _ _ => prod_nonneg fun _ _ => sq_nonneg _)
      (fun k _ => Finset.prod_le_prod (fun _ _ => sq_nonneg _) (fun j _ => pair_bound _ _))
  have e3 : ∏ k, ∏ j ∈ univ.erase k, (2 * ((1 + u k ^ 2) * (1 + u j ^ 2)))
      = ((2 : ℝ) ^ (n - 1)) ^ n * (bigG u ^ (n - 1) * (bigG u ^ n / bigG u)) := by
    simp only [prod_mul_distrib, prod_const, card_erase_of_mem (mem_univ _), card_univ,
      Fintype.card_fin, prod_pow]
    rw [prod_erase_prod (fun k => 1 + u k ^ 2) hg]
    unfold bigG; ring
  have h1 : (1 : ℝ) ≤ bigG u := one_le_bigG u
  have e4 : bigG u ^ (n - 1) * (bigG u ^ n / bigG u) ≤ bigG u ^ (2 * n) := by
    have a : bigG u ^ (n - 1) ≤ bigG u ^ n := pow_le_pow_right₀ h1 (Nat.sub_le n 1)
    have b : bigG u ^ n / bigG u ≤ bigG u ^ n := div_le_self (by positivity) h1
    calc _ ≤ bigG u ^ n * bigG u ^ n :=
          mul_le_mul a b (by positivity) (by positivity)
      _ = _ := by rw [← pow_add]; ring_nf
  have e5 : ((2 : ℝ) ^ (n - 1)) ^ n ≤ ((2 : ℝ) ^ n) ^ n :=
    pow_le_pow_left₀ (by positivity) (pow_le_pow_right₀ (by norm_num) (Nat.sub_le n 1)) n
  rw [e1]
  calc _ ≤ _ := e2
    _ = _ := e3
    _ ≤ _ := mul_le_mul e5 e4 (by positivity) (by positivity)

/-- `w(u) ≤ C / G(u)^2` with `C = 2^{n^2/2}`. -/
lemma huaWeight_le (u : Fin n → ℝ) :
    huaWeight u ≤ Real.sqrt (((2 : ℝ) ^ n) ^ n) / bigG u ^ 2 := by
  have hG := bigG_pos u
  have hw := huaWeight_nonneg u
  have hsq : huaWeight u ^ 2 ≤ (Real.sqrt (((2 : ℝ) ^ n) ^ n) / bigG u ^ 2) ^ 2 := by
    rw [div_pow, Real.sq_sqrt (by positivity)]
    unfold huaWeight
    rw [div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
    calc vdm u ^ 2 * (bigG u ^ 2) ^ 2 ≤ ((2 : ℝ) ^ n) ^ n * bigG u ^ (2 * n) * (bigG u ^ 2) ^ 2 :=
          mul_le_mul_of_nonneg_right (vdm_sq_le u) (by positivity)
      _ = ((2 : ℝ) ^ n) ^ n * (bigG u ^ (n + 2)) ^ 2 := by ring
  exact (pow_le_pow_iff_left₀ hw (by positivity) two_ne_zero).mp hsq

lemma g_le_bigG (u : Fin n → ℝ) (k : Fin n) : 1 + u k ^ 2 ≤ bigG u := by
  unfold bigG
  rw [← mul_prod_erase _ _ (mem_univ k)]
  have : (1 : ℝ) ≤ ∏ x ∈ univ.erase k, (1 + u x ^ 2) :=
    calc (1 : ℝ) = ∏ _x ∈ univ.erase k, (1 : ℝ) := by simp
      _ ≤ _ := Finset.prod_le_prod (fun _ _ => zero_le_one) (fun k _ => one_le_g (u k))
  have := one_le_g (u k)
  nlinarith

lemma sum_sq_le (u : Fin n → ℝ) : ∑ k, u k ^ 2 ≤ n * bigG u := by
  calc ∑ k, u k ^ 2 ≤ ∑ _k : Fin n, bigG u :=
        sum_le_sum fun k _ => by have := g_le_bigG u k; nlinarith
    _ = n * bigG u := by simp

lemma sq_sum_le (u : Fin n → ℝ) : (∑ k, u k) ^ 2 ≤ n * (n * bigG u) := by
  calc (∑ k, u k) ^ 2 ≤ (univ : Finset (Fin n)).card * ∑ k, u k ^ 2 :=
        sq_sum_le_card_mul_sum_sq
    _ ≤ n * (n * bigG u) := by
        simp only [card_univ, Fintype.card_fin]
        exact mul_le_mul_of_nonneg_left (sum_sq_le u) (Nat.cast_nonneg n)

lemma continuous_bigG : Continuous (fun u : Fin n → ℝ => bigG u) := by
  unfold bigG; fun_prop

lemma continuous_huaWeight : Continuous (fun u : Fin n → ℝ => huaWeight u) := by
  have hv : Continuous (fun u : Fin n → ℝ => vdm u) := by unfold vdm; fun_prop
  exact hv.div (continuous_bigG.pow _) fun u => (pow_pos (bigG_pos u) _).ne'

lemma integrable_inv_bigG : Integrable (fun u : Fin n → ℝ => (bigG u)⁻¹) := by
  have e : (fun u : Fin n → ℝ => (bigG u)⁻¹) = fun u => ∏ k, (1 + u k ^ 2)⁻¹ := by
    funext u; unfold bigG; rw [prod_inv_distrib]
  rw [e, volume_pi]
  exact Integrable.fintype_prod (f := fun _ x => (1 + x ^ 2)⁻¹) (μ := fun _ => volume)
    (fun _ => integrable_inv_one_add_sq)

/-- Integrability from a bound `|f| ≤ C / G`. -/
lemma integrable_of_le_inv_bigG (f : (Fin n → ℝ) → ℝ) (hf : Continuous f) (C : ℝ)
    (hb : ∀ u, |f u| ≤ C * (bigG u)⁻¹) : Integrable f :=
  Integrable.mono' (integrable_inv_bigG.const_mul C) hf.aestronglyMeasurable
    (Filter.Eventually.of_forall fun u => by simpa [Real.norm_eq_abs] using hb u)

lemma weight_le_inv (u : Fin n → ℝ) :
    huaWeight u ≤ Real.sqrt (((2 : ℝ) ^ n) ^ n) * (bigG u)⁻¹ := by
  have hG := one_le_bigG u
  calc huaWeight u ≤ Real.sqrt (((2 : ℝ) ^ n) ^ n) / bigG u ^ 2 := huaWeight_le u
    _ ≤ Real.sqrt (((2 : ℝ) ^ n) ^ n) / bigG u :=
        div_le_div_of_nonneg_left (Real.sqrt_nonneg _) (by positivity)
          (by nlinarith)
    _ = _ := by ring

lemma weight_mul_le (u : Fin n → ℝ) (q : ℝ) (hq0 : 0 ≤ q) (D : ℝ) (hq : q ≤ D * bigG u) :
    huaWeight u * q ≤ Real.sqrt (((2 : ℝ) ^ n) ^ n) * D * (bigG u)⁻¹ := by
  have hG := bigG_pos u
  have hD : 0 ≤ D := by
    by_contra h; push Not at h; nlinarith
  calc huaWeight u * q ≤ (Real.sqrt (((2 : ℝ) ^ n) ^ n) / bigG u ^ 2) * (D * bigG u) :=
        mul_le_mul (huaWeight_le u) hq hq0 (by positivity)
    _ = Real.sqrt (((2 : ℝ) ^ n) ^ n) * D * (bigG u)⁻¹ := by field_simp

lemma integrable_huaWeight : Integrable (fun u : Fin n → ℝ => huaWeight u) :=
  integrable_of_le_inv_bigG _ continuous_huaWeight _ fun u => by
    rw [abs_of_nonneg (huaWeight_nonneg u)]; exact weight_le_inv u

/-- The coincidence set `{u_i = u_j}` for `i ≠ j` is Lebesgue-null. -/
lemma volume_diag_eq_zero {i j : Fin n} (hij : i ≠ j) :
    volume {u : Fin n → ℝ | u i = u j} = 0 := by
  let L : (Fin n → ℝ) →ₗ[ℝ] ℝ := LinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i
    - LinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) j
  have hs : {u : Fin n → ℝ | u i = u j} = (LinearMap.ker L : Set (Fin n → ℝ)) := by
    ext u; simp [L, sub_eq_zero]
  rw [hs]
  apply Measure.addHaar_submodule
  intro htop
  have : (Pi.single i (1 : ℝ) : Fin n → ℝ) ∈ LinearMap.ker L := by rw [htop]; trivial
  simp [L, Pi.single_apply, hij.symm] at this

lemma ae_injective_volume : ∀ᵐ u : Fin n → ℝ, Function.Injective u := by
  rw [ae_iff]
  apply measure_mono_null (t := ⋃ i : Fin n, ⋃ j : Fin n, ⋃ (_ : i ≠ j), {u | u i = u j})
  · intro u hu
    simp only [Function.Injective, not_forall, Set.mem_ofPred_eq] at hu
    obtain ⟨i, j, h, hne⟩ := hu
    simp only [Set.mem_iUnion]
    exact ⟨i, j, hne, h⟩
  · simp only [measure_iUnion_null_iff]
    intro i j hij
    exact volume_diag_eq_zero hij

lemma vdm_pos {u : Fin n → ℝ} (hu : Function.Injective u) : 0 < vdm u :=
  prod_pos fun k _ => prod_pos fun j hj =>
    abs_pos.mpr (sub_ne_zero.mpr (hu.ne (ne_of_mem_erase hj).symm))

lemma huaZ_pos : 0 < huaZ n := by
  unfold huaZ
  rw [integral_pos_iff_support_of_nonneg (fun u => huaWeight_nonneg u) integrable_huaWeight]
  have hsub : {u : Fin n → ℝ | ¬ Function.Injective u}ᶜ ⊆ Function.support huaWeight := by
    intro u hu
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_not] at hu
    exact (div_pos (vdm_pos hu) (pow_pos (bigG_pos u) _)).ne'
  have hnull : volume {u : Fin n → ℝ | ¬ Function.Injective u} = 0 := ae_iff.mp ae_injective_volume
  have huniv : volume (Set.univ : Set (Fin n → ℝ)) ≠ 0 :=
    isOpen_univ.measure_ne_zero volume Set.univ_nonempty
  refine pos_iff_ne_zero.mpr fun h0 => huniv ?_
  apply measure_mono_null (t := {u : Fin n → ℝ | ¬ Function.Injective u} ∪ Function.support huaWeight)
  · intro u _
    by_cases h : Function.Injective u
    · exact Or.inr (hsub (by simpa using h))
    · exact Or.inl h
  · exact measure_union_null hnull h0

lemma coe_huaDensity (u : Fin n → ℝ) : (huaDensity u : ℝ) = huaWeight u / huaZ n :=
  Real.coe_toNNReal _ (div_nonneg (huaWeight_nonneg u) huaZ_pos.le)

lemma measurable_huaDensity : Measurable (fun u : Fin n → ℝ => huaDensity u) :=
  ((continuous_huaWeight.div_const _).measurable).real_toNNReal

instance : IsProbabilityMeasure (huaMeasure n) := by
  constructor
  rw [huaMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    lintegral_coe_eq_integral]
  · simp only [coe_huaDensity]
    rw [integral_div, ← huaZ, div_self huaZ_pos.ne', ENNReal.ofReal_one]
  · simpa [coe_huaDensity] using integrable_huaWeight.div_const (huaZ n)

theorem huaMeasure_ae_injective : ∀ᵐ u ∂(huaMeasure n), Function.Injective u :=
  (withDensity_absolutelyContinuous _ _).ae_le ae_injective_volume

lemma integrable_hua_iff (f : (Fin n → ℝ) → ℝ) :
    Integrable f (huaMeasure n) ↔ Integrable (fun u => huaWeight u / huaZ n * f u) := by
  rw [huaMeasure, integrable_withDensity_iff_integrable_smul measurable_huaDensity]
  simp [NNReal.smul_def, coe_huaDensity]

theorem huaMeasure_int_sq_sum :
    Integrable (fun u : Fin n → ℝ => (∑ k, u k) ^ 2) (huaMeasure n) := by
  rw [integrable_hua_iff]
  have : Integrable (fun u : Fin n → ℝ => huaWeight u * (∑ k, u k) ^ 2) :=
    integrable_of_le_inv_bigG _ (by have := continuous_huaWeight (n := n); fun_prop)
      (Real.sqrt (((2 : ℝ) ^ n) ^ n) * (n * n)) fun u => by
        rw [abs_of_nonneg (mul_nonneg (huaWeight_nonneg u) (sq_nonneg _))]
        exact weight_mul_le u _ (sq_nonneg _) _ (by have := sq_sum_le u; linarith)
  exact (this.div_const (huaZ n)).congr (Filter.Eventually.of_forall fun u => by ring)

theorem huaMeasure_int_sum_sq :
    Integrable (fun u : Fin n → ℝ => ∑ k, u k ^ 2) (huaMeasure n) := by
  rw [integrable_hua_iff]
  have : Integrable (fun u : Fin n → ℝ => huaWeight u * ∑ k, u k ^ 2) :=
    integrable_of_le_inv_bigG _ (by have := continuous_huaWeight (n := n); fun_prop)
      (Real.sqrt (((2 : ℝ) ^ n) ^ n) * n) fun u => by
        rw [abs_of_nonneg (mul_nonneg (huaWeight_nonneg u)
          (sum_nonneg fun _ _ => sq_nonneg _))]
        exact weight_mul_le u _ (sum_nonneg fun _ _ => sq_nonneg _) _ (sum_sq_le u)
  exact (this.div_const (huaZ n)).congr (Filter.Eventually.of_forall fun u => by ring)

end Singh





/-!
Loop equations for the Hua ensemble via integration by parts.
-/

open MeasureTheory Finset Filter
open scoped ENNReal NNReal

namespace Singh

variable {n : ℕ}


lemma sum_offdiag_eq_two_pairs (g : Fin n → Fin n → ℝ) (hg : ∀ a b, g a b = g b a) :
    ∑ a, ∑ b ∈ univ.erase a, g a b = 2 * ∑ p ∈ pairs n, g p.1 p.2 := by
  have h1 : ∀ a, ∑ b ∈ univ.erase a, g a b = ∑ b, if a ≠ b then g a b else 0 := by
    intro a; rw [← sum_filter, filter_ne]
  simp only [h1]
  rw [← Fintype.sum_prod_type' (fun a b => if a ≠ b then g a b else 0)]
  have h2 : ∀ p : Fin n × Fin n, (if p.1 ≠ p.2 then g p.1 p.2 else 0)
      = (if p.1 < p.2 then g p.1 p.2 else 0) + (if p.2 < p.1 then g p.1 p.2 else 0) := by
    intro p
    by_cases a : p.1 < p.2
    · simp [a, ne_of_lt a, not_lt_of_gt a]
    · by_cases b : p.2 < p.1
      · simp [a, b, ne_of_gt b]
      · have : p.1 = p.2 := le_antisymm (not_lt.mp b) (not_lt.mp a)
        simp [this]
  simp only [h2, sum_add_distrib]
  have h3 : ∑ p : Fin n × Fin n, (if p.2 < p.1 then g p.1 p.2 else 0)
      = ∑ p : Fin n × Fin n, (if p.1 < p.2 then g p.1 p.2 else 0) :=
    Fintype.sum_equiv (Equiv.prodComm _ _) _ _ fun p => by
      rcases p with ⟨a, b⟩; by_cases h : b < a <;> simp [h, hg a b]
  rw [h3, pairs, sum_filter]; ring

lemma prod_offdiag_eq_sq_pairs (g : Fin n → Fin n → ℝ) (hg : ∀ a b, g a b = g b a) :
    ∏ a, ∏ b ∈ univ.erase a, g a b = (∏ p ∈ pairs n, g p.1 p.2) ^ 2 := by
  have h1 : ∀ a, ∏ b ∈ univ.erase a, g a b = ∏ b, if a ≠ b then g a b else 1 := by
    intro a; rw [← prod_filter, filter_ne]
  simp only [h1]
  rw [← Fintype.prod_prod_type' (fun a b => if a ≠ b then g a b else 1)]
  have h2 : ∀ p : Fin n × Fin n, (if p.1 ≠ p.2 then g p.1 p.2 else 1)
      = (if p.1 < p.2 then g p.1 p.2 else 1) * (if p.2 < p.1 then g p.1 p.2 else 1) := by
    intro p
    by_cases a : p.1 < p.2
    · simp [a, ne_of_lt a, not_lt_of_gt a]
    · by_cases b : p.2 < p.1
      · simp [a, b, ne_of_gt b]
      · have : p.1 = p.2 := le_antisymm (not_lt.mp b) (not_lt.mp a)
        simp [this]
  simp only [h2, prod_mul_distrib]
  have h3 : ∏ p : Fin n × Fin n, (if p.2 < p.1 then g p.1 p.2 else 1)
      = ∏ p : Fin n × Fin n, (if p.1 < p.2 then g p.1 p.2 else 1) :=
    Fintype.prod_equiv (Equiv.prodComm _ _) _ _ fun p => by
      rcases p with ⟨a, b⟩; by_cases h : b < a <;> simp [h, hg a b]
  rw [h3, pairs, prod_filter]; ring

/-- Squared Vandermonde as a polynomial. -/
noncomputable def Wp (u : Fin n → ℝ) : ℝ := ∏ p ∈ pairs n, (u p.1 - u p.2) ^ 2

lemma vdm_eq_Wp (u : Fin n → ℝ) : vdm u = Wp u := by
  unfold vdm Wp
  rw [prod_offdiag_eq_sq_pairs (fun a b => |u a - u b|) (fun a b => abs_sub_comm _ _),
    ← prod_pow]
  exact prod_congr rfl fun p _ => sq_abs _


/-- Coordinate of the direction `e_k`. -/
def dlt (k a : Fin n) : ℝ := if a = k then 1 else 0

lemma line_apply (u : Fin n → ℝ) (k a : Fin n) (t : ℝ) :
    (u + t • (Pi.single k (1 : ℝ) : Fin n → ℝ)) a = u a + t * dlt k a := by
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, dlt]

/-- One-variable factor `(1+x^2)^{-(n+2)}`. -/
noncomputable def qf (n : ℕ) (x : ℝ) : ℝ := ((1 + x ^ 2) ^ (n + 2))⁻¹

/-- `G^{-(n+2)}` as a product. -/
noncomputable def Hn (u : Fin n → ℝ) : ℝ := ∏ a, qf n (u a)

lemma Hn_eq (u : Fin n → ℝ) : Hn u = (bigG u ^ (n + 2))⁻¹ := by
  unfold Hn qf bigG; rw [prod_inv_distrib, prod_pow]

lemma Hn_pos (u : Fin n → ℝ) : 0 < Hn u := by
  rw [Hn_eq]; have := bigG_pos u; positivity

lemma huaWeight_eq (u : Fin n → ℝ) : huaWeight u = Wp u * Hn u := by
  rw [huaWeight, vdm_eq_Wp, Hn_eq, div_eq_mul_inv]

/-- Derivative of `Wp` along `e_k`. -/
noncomputable def dWp (k : Fin n) (u : Fin n → ℝ) : ℝ :=
  ∑ p ∈ pairs n, (∏ p' ∈ (pairs n).erase p, (u p'.1 - u p'.2) ^ 2)
    * (2 * (u p.1 - u p.2) * (dlt k p.1 - dlt k p.2))

/-- Derivative of `Hn` along `e_k`. -/
noncomputable def dHn (k : Fin n) (u : Fin n → ℝ) : ℝ :=
  -(2 * ((n : ℝ) + 2) * u k) / (1 + u k ^ 2) * Hn u

lemma hasLineDerivAt_Wp (k : Fin n) (u : Fin n → ℝ) :
    HasLineDerivAt ℝ Wp (dWp k u) u (Pi.single k 1) := by
  unfold HasLineDerivAt
  have e : (fun t : ℝ => Wp (u + t • Pi.single k (1 : ℝ))) = fun t =>
      ∏ p ∈ pairs n, ((u p.1 - u p.2) + t * (dlt k p.1 - dlt k p.2)) ^ 2 := by
    funext t; unfold Wp; refine prod_congr rfl fun p _ => ?_
    rw [line_apply, line_apply]; ring
  rw [e]
  have h : ∀ p ∈ pairs n, HasDerivAt (fun t : ℝ => ((u p.1 - u p.2) + t * (dlt k p.1 - dlt k p.2)) ^ 2)
      (2 * (u p.1 - u p.2) * (dlt k p.1 - dlt k p.2)) 0 := by
    intro p _
    have := (((hasDerivAt_id (0 : ℝ)).mul_const (dlt k p.1 - dlt k p.2)).const_add
      (u p.1 - u p.2)).pow 2
    convert this using 1 <;> try with_reducible_and_instances rfl
    · funext t; simp only [Pi.pow_apply, id]
    · simp
  convert HasDerivAt.fun_finsetProd h using 1 <;> try with_reducible_and_instances rfl
  unfold dWp; refine sum_congr rfl fun p _ => ?_
  simp [smul_eq_mul]

lemma hasDerivAt_qf (x : ℝ) :
    HasDerivAt (qf n) (-(2 * ((n : ℝ) + 2) * x) / (1 + x ^ 2) * qf n x) x := by
  have hc : HasDerivAt (fun y : ℝ => (1 + y ^ 2) ^ (n + 2))
      (((n + 2 : ℕ) : ℝ) * (1 + x ^ 2) ^ (n + 2 - 1) * (2 * x)) x := by
    have := ((hasDerivAt_pow 2 x).const_add 1).pow (n + 2)
    convert this using 1 <;> (try with_reducible_and_instances rfl) <;> (try rfl) <;> norm_num
  have hx : (1 + x ^ 2) ^ (n + 2) ≠ 0 := by positivity
  convert hc.inv hx using 1 <;> try with_reducible_and_instances rfl
  have h1 : (0 : ℝ) < 1 + x ^ 2 := by positivity
  · rfl
  unfold qf
  rw [show n + 2 - 1 = n + 1 from rfl]
  field_simp
  push_cast
  ring

lemma hasLineDerivAt_Hn (k : Fin n) (u : Fin n → ℝ) :
    HasLineDerivAt ℝ Hn (dHn k u) u (Pi.single k 1) := by
  unfold HasLineDerivAt
  have e : (fun t : ℝ => Hn (u + t • Pi.single k (1 : ℝ))) = fun t =>
      qf n (u k + t) * ∏ a ∈ univ.erase k, qf n (u a) := by
    funext t; unfold Hn
    rw [← mul_prod_erase univ (fun a => qf n ((u + t • (Pi.single k (1 : ℝ) : Fin n → ℝ)) a))
      (mem_univ k)]
    simp only [line_apply, dlt, ite_true, mul_one]
    congr 1
    refine prod_congr rfl fun a ha => ?_
    simp [ne_of_mem_erase ha]
  rw [e]
  have h0 : HasDerivAt (fun t : ℝ => u k + t) 1 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_add (u k)
  have hq : HasDerivAt (qf n) (-(2 * ((n : ℝ) + 2) * u k) / (1 + u k ^ 2) * qf n (u k))
      (u k + 0) := by rw [add_zero]; exact hasDerivAt_qf (u k)
  have := (hq.comp (0 : ℝ) h0).mul_const (∏ a ∈ univ.erase k, qf n (u a))
  convert this using 1 <;> try with_reducible_and_instances rfl
  · funext t; simp
  · unfold dHn Hn; rw [← mul_prod_erase _ _ (mem_univ k)]; simp; ring


lemma dWp_eq (k : Fin n) (u : Fin n → ℝ) (hu : Function.Injective u) :
    dWp k u = Wp u * ∑ j ∈ univ.erase k, 2 / (u k - u j) := by
  have hne : ∀ p ∈ pairs n, u p.1 - u p.2 ≠ 0 := fun p hp =>
    sub_ne_zero.mpr fun h => (ne_of_lt (mem_filter.mp hp).2) (hu h)
  have e1 : ∀ p ∈ pairs n, ∏ p' ∈ (pairs n).erase p, (u p'.1 - u p'.2) ^ 2
      = Wp u / (u p.1 - u p.2) ^ 2 := fun p hp => by
    rw [eq_div_iff (pow_ne_zero 2 (hne p hp)), Wp, ← mul_prod_erase _ _ hp, mul_comm]
  have e2 : dWp k u
      = Wp u * ∑ p ∈ pairs n, (2 * dlt k p.1 - 2 * dlt k p.2) / (u p.1 - u p.2) := by
    unfold dWp; rw [mul_sum]; refine sum_congr rfl fun p hp => ?_
    rw [e1 p hp]; have := hne p hp; field_simp
  rw [e2]; congr 1
  have h3 := sum_offdiag_eq_two_pairs (fun a b => (2 * dlt k a - 2 * dlt k b) / (u a - u b))
    (fun a b => by
      rw [show 2 * dlt k b - 2 * dlt k a = -(2 * dlt k a - 2 * dlt k b) by ring,
        show u b - u a = -(u a - u b) by ring, neg_div_neg_eq])
  have h4 := pair_sum_symm u (fun a => 2 * dlt k a)
  have h5 : ∑ a, ∑ b ∈ univ.erase a, 2 * dlt k a / (u a - u b)
      = ∑ j ∈ univ.erase k, 2 / (u k - u j) := by
    simp only [dlt, mul_ite, mul_one, mul_zero, ite_div, zero_div]
    rw [Fintype.sum_eq_single k]
    · simp
    · intro x hx; simp [hx]
  linarith

lemma pairs_prod_g (u : Fin n → ℝ) :
    ∏ p ∈ pairs n, ((1 + u p.1 ^ 2) * (1 + u p.2 ^ 2)) = bigG u ^ n / bigG u := by
  have hg : ∀ k, 0 < 1 + u k ^ 2 := fun k => by positivity
  have hG := bigG_pos u
  have hsq : (∏ p ∈ pairs n, ((1 + u p.1 ^ 2) * (1 + u p.2 ^ 2))) ^ 2
      = (bigG u ^ n / bigG u) ^ 2 := by
    rw [← prod_offdiag_eq_sq_pairs (fun a b => (1 + u a ^ 2) * (1 + u b ^ 2))
      (fun a b => mul_comm _ _)]
    simp only [prod_mul_distrib, prod_const, card_erase_of_mem (mem_univ _), card_univ,
      Fintype.card_fin, prod_pow]
    rw [prod_erase_prod (fun k => 1 + u k ^ 2) hg]
    change bigG u ^ (n - 1) * (bigG u ^ n / bigG u) = _
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp [bigG]
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      simp only [Nat.add_sub_cancel, pow_succ]
      field_simp
  exact (pow_left_inj₀ (prod_nonneg fun p _ => by positivity) (by positivity)
    two_ne_zero).mp hsq

lemma factor_le (a b : ℝ) : (a - b) ^ 2 ≤ 6 * ((1 + a ^ 2) * (1 + b ^ 2)) := by
  have := pair_bound a b
  have : 0 ≤ (1 + a ^ 2) * (1 + b ^ 2) := by positivity
  linarith

lemma abs_le_one_add_sq (x : ℝ) : |x| ≤ 1 + x ^ 2 := by
  nlinarith [sq_nonneg (|x| - 1), sq_abs x, abs_nonneg x]

lemma dfactor_le (a b d : ℝ) (hd : |d| ≤ 1) :
    |2 * (a - b) * d| ≤ 6 * ((1 + a ^ 2) * (1 + b ^ 2)) := by
  have h1 : 2 * |a - b| ≤ 1 + (a - b) ^ 2 := by
    nlinarith [sq_nonneg (|a - b| - 1), sq_abs (a - b)]
  have hg : 1 ≤ (1 + a ^ 2) * (1 + b ^ 2) :=
    one_le_mul_of_one_le_of_one_le (one_le_g a) (one_le_g b)
  rw [abs_mul, abs_mul, abs_two]
  nlinarith [abs_nonneg (a - b), abs_nonneg d, pair_bound a b,
    mul_le_mul_of_nonneg_left hd (abs_nonneg (a - b))]

lemma dlt_sub_le (k a b : Fin n) : |dlt k a - dlt k b| ≤ 1 := by
  unfold dlt; split_ifs <;> norm_num

/-- `∏_{a<b} 6 (1+u_a^2)(1+u_b^2) = 6^{#pairs} G^{n-1}`. -/
lemma Kp_eq (u : Fin n → ℝ) :
    ∏ p ∈ pairs n, (6 * ((1 + u p.1 ^ 2) * (1 + u p.2 ^ 2)))
      = 6 ^ (pairs n).card * (bigG u ^ n / bigG u) := by
  rw [prod_mul_distrib, prod_const, pairs_prod_g]

lemma Wp_nonneg (u : Fin n → ℝ) : 0 ≤ Wp u := prod_nonneg fun _ _ => sq_nonneg _

lemma Wp_le (u : Fin n → ℝ) :
    Wp u ≤ 6 ^ (pairs n).card * (bigG u ^ n / bigG u) := by
  rw [← Kp_eq]
  exact Finset.prod_le_prod (fun _ _ => sq_nonneg _) fun p _ => factor_le _ _

lemma abs_dWp_le (k : Fin n) (u : Fin n → ℝ) :
    |dWp k u| ≤ (pairs n).card * (6 ^ (pairs n).card * (bigG u ^ n / bigG u)) := by
  rw [← Kp_eq]
  unfold dWp
  refine (abs_sum_le_sum_abs _ _).trans ?_
  rw [← nsmul_eq_mul, ← sum_const]
  refine sum_le_sum fun p hp => ?_
  rw [abs_mul, abs_of_nonneg (prod_nonneg fun _ _ => sq_nonneg _), ← prod_erase_mul _ _ hp]
  exact mul_le_mul
    (Finset.prod_le_prod (fun _ _ => sq_nonneg _) fun q _ => factor_le _ _)
    (dfactor_le _ _ _ (dlt_sub_le _ _ _)) (abs_nonneg _)
    (prod_nonneg fun _ _ => by positivity)

lemma abs_dHn_le (k : Fin n) (u : Fin n → ℝ) : |dHn k u| ≤ ((n : ℝ) + 2) * Hn u := by
  have hH := Hn_pos u
  have hg : 0 < 1 + u k ^ 2 := by positivity
  unfold dHn
  rw [abs_mul, abs_of_pos hH]
  refine mul_le_mul_of_nonneg_right ?_ hH.le
  rw [abs_div, abs_neg, abs_of_pos hg, div_le_iff₀ hg, abs_mul,
    abs_of_pos (by positivity : (0 : ℝ) < 2 * ((n : ℝ) + 2))]
  have h1 : 2 * |u k| ≤ 1 + u k ^ 2 := by
    nlinarith [sq_nonneg (|u k| - 1), sq_abs (u k)]
  have hn : (0 : ℝ) ≤ (n : ℝ) + 2 := by positivity
  nlinarith

lemma G_scale (u : Fin n → ℝ) : bigG u ^ 2 * (bigG u ^ n / bigG u) * Hn u = (bigG u)⁻¹ := by
  rw [Hn_eq]; have := bigG_pos u; field_simp; ring

lemma measurable_Wp : Measurable (fun u : Fin n → ℝ => Wp u) := by unfold Wp; fun_prop
lemma measurable_dWp (k : Fin n) : Measurable (fun u : Fin n → ℝ => dWp k u) := by
  unfold dWp; fun_prop
lemma measurable_Hn : Measurable (fun u : Fin n → ℝ => Hn u) := by unfold Hn qf; fun_prop
lemma measurable_dHn (k : Fin n) : Measurable (fun u : Fin n → ℝ => dHn k u) := by
  unfold dHn; have := measurable_Hn (n := n); fun_prop

lemma integrable_of_le_inv_bigG' (f : (Fin n → ℝ) → ℝ) (hf : Measurable f) (C : ℝ)
    (hb : ∀ u, |f u| ≤ C * (bigG u)⁻¹) : Integrable f :=
  Integrable.mono' (integrable_inv_bigG.const_mul C) hf.aestronglyMeasurable
    (Eventually.of_forall fun u => by simpa [Real.norm_eq_abs] using hb u)

/-- A line derivative of an integrable function with integrable derivative integrates to zero. -/
lemma integral_lineDeriv_eq_zero {f f' : (Fin n → ℝ) → ℝ} (v : Fin n → ℝ)
    (hf : ∀ x, HasLineDerivAt ℝ f (f' x) x v) (hi : Integrable f) (hi' : Integrable f') :
    ∫ x, f' x = 0 := by
  have := integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
    (μ := volume) (B := ContinuousLinearMap.mul ℝ ℝ) (f := f) (f' := f')
    (g := fun _ => (1 : ℝ)) (g' := fun _ => (0 : ℝ)) (v := v)
    (by simpa using hi') (by simp) (by simpa using hi) (fun x _ => hf x)
    (fun x _ => hasDerivAt_const _ _)
  simp at this
  linarith

/-- The divergence term `∂_k (A · Wp · Hn)`. -/
noncomputable def loopD (k : Fin n) (A A' : (Fin n → ℝ) → ℝ) (u : Fin n → ℝ) : ℝ :=
  A' u * Wp u * Hn u + A u * dWp k u * Hn u + A u * Wp u * dHn k u

section generic

variable (k : Fin n) (A A' : (Fin n → ℝ) → ℝ) (a : ℝ)

lemma loopD_bound (ha : 0 ≤ a) (hAb : ∀ u, |A u| ≤ a * bigG u ^ 2)
    (hA'b : ∀ u, |A' u| ≤ a * bigG u ^ 2) (u : Fin n → ℝ) :
    |loopD k A A' u| ≤ a * 6 ^ (pairs n).card * (1 + (pairs n).card + ((n : ℝ) + 2))
      * (bigG u)⁻¹ := by
  have hW0 := Wp_nonneg u
  have hW := Wp_le u
  have hdW := abs_dWp_le k u
  have hdH := abs_dHn_le k u
  have hH := Hn_pos u
  have hG := bigG_pos u
  set K := 6 ^ (pairs n).card * (bigG u ^ n / bigG u) with hK
  have hK0 : 0 ≤ K := by positivity
  have hc : (0 : ℝ) ≤ (pairs n).card := by positivity
  have t1 : |A' u * Wp u * Hn u| ≤ a * bigG u ^ 2 * K * Hn u := by
    rw [abs_mul, abs_mul, abs_of_nonneg hW0, abs_of_pos hH]
    exact mul_le_mul_of_nonneg_right (mul_le_mul (hA'b u) hW hW0 (by positivity)) hH.le
  have t2 : |A u * dWp k u * Hn u| ≤ a * bigG u ^ 2 * ((pairs n).card * K) * Hn u := by
    rw [abs_mul, abs_mul, abs_of_pos hH]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul (hAb u) hdW (abs_nonneg _) (by positivity)) hH.le
  have t3 : |A u * Wp u * dHn k u| ≤ a * bigG u ^ 2 * K * (((n : ℝ) + 2) * Hn u) := by
    rw [abs_mul, abs_mul, abs_of_nonneg hW0]
    exact mul_le_mul (mul_le_mul (hAb u) hW hW0 (by positivity)) hdH (abs_nonneg _)
      (by positivity)
  have hs := G_scale u
  calc |loopD k A A' u|
      ≤ |A' u * Wp u * Hn u| + |A u * dWp k u * Hn u| + |A u * Wp u * dHn k u| :=
        (abs_add_le _ _).trans (add_le_add_left (abs_add_le _ _) _) |>.trans_eq (by ring)
    _ ≤ a * bigG u ^ 2 * K * Hn u + a * bigG u ^ 2 * ((pairs n).card * K) * Hn u
        + a * bigG u ^ 2 * K * (((n : ℝ) + 2) * Hn u) := by linarith
    _ = a * 6 ^ (pairs n).card * (1 + (pairs n).card + ((n : ℝ) + 2))
        * (bigG u ^ 2 * (bigG u ^ n / bigG u) * Hn u) := by rw [hK]; ring
    _ = _ := by rw [hs]

lemma loopF_bound (ha : 0 ≤ a) (hAb : ∀ u, |A u| ≤ a * bigG u ^ 2) (u : Fin n → ℝ) :
    |A u * Wp u * Hn u| ≤ a * 6 ^ (pairs n).card * (bigG u)⁻¹ := by
  have hW0 := Wp_nonneg u
  have hH := Hn_pos u
  have hG := bigG_pos u
  rw [abs_mul, abs_mul, abs_of_nonneg hW0, abs_of_pos hH, ← G_scale u]
  calc |A u| * Wp u * Hn u ≤ a * bigG u ^ 2 * (6 ^ (pairs n).card * (bigG u ^ n / bigG u))
        * Hn u :=
        mul_le_mul_of_nonneg_right (mul_le_mul (hAb u) (Wp_le u) hW0 (by positivity)) hH.le
    _ = _ := by ring

variable (hA : ∀ u, HasLineDerivAt ℝ A (A' u) u (Pi.single k 1))
  (hAm : Measurable A) (hA'm : Measurable A') (ha : 0 ≤ a)
  (hAb : ∀ u, |A u| ≤ a * bigG u ^ 2) (hA'b : ∀ u, |A' u| ≤ a * bigG u ^ 2)
include hA'm hAm ha hAb hA'b

lemma integrable_loopD : Integrable (fun u => loopD k A A' u) :=
  integrable_of_le_inv_bigG' _ (by
    unfold loopD
    have := measurable_Wp (n := n); have := measurable_Hn (n := n)
    have := measurable_dWp k; have := measurable_dHn k
    fun_prop) _ (loopD_bound k A A' a ha hAb hA'b)

include hA in
lemma integral_loopD : ∫ u, loopD k A A' u = 0 := by
  refine integral_lineDeriv_eq_zero (f := fun u => A u * Wp u * Hn u) (Pi.single k 1)
    (fun u => ?_) ?_ (integrable_loopD k A A' a hAm hA'm ha hAb hA'b)
  · have := ((hA u).mul (hasLineDerivAt_Wp k u)).mul (hasLineDerivAt_Hn k u)
    simp only [zero_smul, add_zero] at this
    unfold HasLineDerivAt
    convert this using 1 <;> try with_reducible_and_instances rfl
    unfold loopD; simp only [Pi.mul_apply, zero_smul, add_zero]; ring
  · exact integrable_of_le_inv_bigG' _ (by
      have := measurable_Wp (n := n); have := measurable_Hn (n := n); fun_prop) _
      (loopF_bound A a ha hAb)

end generic


lemma abs_sum_le_bigG (u : Fin n → ℝ) : |∑ j, u j| ≤ n * bigG u := by
  refine (abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ j, |u j| ≤ ∑ _j : Fin n, bigG u :=
        sum_le_sum fun j _ => (abs_le_one_add_sq _).trans (g_le_bigG u j)
    _ = n * bigG u := by simp

lemma bigG_le_sq (u : Fin n → ℝ) : bigG u ≤ bigG u ^ 2 := by
  have := one_le_bigG u; nlinarith

lemma sum_line (u : Fin n → ℝ) (k : Fin n) (t : ℝ) :
    ∑ j, (u + t • (Pi.single k (1 : ℝ) : Fin n → ℝ)) j = ∑ j, u j + t := by
  simp only [line_apply, sum_add_distrib, ← mul_sum]; simp [dlt]

/-- Field for loop equation (a). -/
noncomputable def fieldA (k : Fin n) (u : Fin n → ℝ) : ℝ := (1 + u k ^ 2) * ∑ j, u j
noncomputable def fieldA' (k : Fin n) (u : Fin n → ℝ) : ℝ :=
  2 * u k * ∑ j, u j + (1 + u k ^ 2)

/-- Field for loop equation (b). -/
noncomputable def fieldB (k : Fin n) (u : Fin n → ℝ) : ℝ := (1 + u k ^ 2) * u k
noncomputable def fieldB' (k : Fin n) (u : Fin n → ℝ) : ℝ := 1 + 3 * u k ^ 2

lemma hasLineDerivAt_fieldA (k : Fin n) (u : Fin n → ℝ) :
    HasLineDerivAt ℝ (fieldA k) (fieldA' k u) u (Pi.single k 1) := by
  unfold HasLineDerivAt
  have e : (fun t : ℝ => fieldA k (u + t • Pi.single k (1 : ℝ))) =
      fun t => (1 + (u k + t) * (u k + t)) * (∑ j, u j + t) := by
    funext t; unfold fieldA; rw [sum_line, line_apply, dlt, if_pos rfl]; ring
  rw [e]
  have h0 := (hasDerivAt_id (0 : ℝ)).const_add (u k)
  have h1 := (hasDerivAt_id (0 : ℝ)).const_add (∑ j, u j)
  have := ((h0.mul h0).const_add 1).mul h1
  convert this using 1 <;> try with_reducible_and_instances rfl
  · funext t; simp only [Pi.mul_apply, id]
  · unfold fieldA'; simp; ring

lemma hasLineDerivAt_fieldB (k : Fin n) (u : Fin n → ℝ) :
    HasLineDerivAt ℝ (fieldB k) (fieldB' k u) u (Pi.single k 1) := by
  unfold HasLineDerivAt
  have e : (fun t : ℝ => fieldB k (u + t • Pi.single k (1 : ℝ))) =
      fun t => (1 + (u k + t) * (u k + t)) * (u k + t) := by
    funext t; unfold fieldB; rw [line_apply, dlt, if_pos rfl]; ring
  rw [e]
  have h0 := (hasDerivAt_id (0 : ℝ)).const_add (u k)
  have := ((h0.mul h0).const_add 1).mul h0
  convert this using 1 <;> try with_reducible_and_instances rfl
  · funext t; simp only [Pi.mul_apply, id]
  · unfold fieldB'; simp; ring

lemma fieldA_bound (k : Fin n) (u : Fin n → ℝ) :
    |fieldA k u| ≤ (2 * n + 1) * bigG u ^ 2 := by
  have hg := g_le_bigG u k
  have hs := abs_sum_le_bigG u
  have hG := one_le_bigG u
  unfold fieldA
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 + u k ^ 2)]
  calc (1 + u k ^ 2) * |∑ j, u j| ≤ bigG u * (n * bigG u) :=
        mul_le_mul hg hs (abs_nonneg _) (by positivity)
    _ ≤ (2 * n + 1) * bigG u ^ 2 := by nlinarith [sq_nonneg (bigG u)]

lemma fieldA'_bound (k : Fin n) (u : Fin n → ℝ) :
    |fieldA' k u| ≤ (2 * n + 1) * bigG u ^ 2 := by
  have hg := g_le_bigG u k
  have hs := abs_sum_le_bigG u
  have hG := one_le_bigG u
  have hu := (abs_le_one_add_sq (u k)).trans hg
  have hsq := bigG_le_sq u
  unfold fieldA'
  calc |2 * u k * ∑ j, u j + (1 + u k ^ 2)|
      ≤ 2 * |u k| * |∑ j, u j| + (1 + u k ^ 2) := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_mul, abs_two, abs_of_pos (by positivity : (0 : ℝ) < 1 + u k ^ 2)]
    _ ≤ 2 * bigG u * (n * bigG u) + bigG u := by
        have := mul_le_mul hu hs (abs_nonneg _) (by positivity)
        linarith
    _ ≤ (2 * n + 1) * bigG u ^ 2 := by nlinarith

lemma fieldB_bound (k : Fin n) (u : Fin n → ℝ) : |fieldB k u| ≤ 3 * bigG u ^ 2 := by
  have hg := g_le_bigG u k
  have hu := (abs_le_one_add_sq (u k)).trans hg
  have hG := one_le_bigG u
  unfold fieldB
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 + u k ^ 2)]
  have := mul_le_mul hg hu (abs_nonneg _) (by positivity)
  nlinarith

lemma fieldB'_bound (k : Fin n) (u : Fin n → ℝ) : |fieldB' k u| ≤ 3 * bigG u ^ 2 := by
  have hg := g_le_bigG u k
  have hsq := bigG_le_sq u
  unfold fieldB'
  rw [abs_of_pos (by positivity)]
  nlinarith [sq_nonneg (u k)]

lemma pointwise_A (k : Fin n) (u : Fin n → ℝ) (hu : Function.Injective u) :
    huaWeight u * (2 * u k * (∑ j, u j) + (1 + u k ^ 2)
        + (1 + u k ^ 2) * (∑ j, u j) * logDeriv 2 u k)
      = loopD k (fieldA k) (fieldA' k) u := by
  rw [huaWeight_eq, loopD, dWp_eq k u hu, dHn, logDeriv, fieldA, fieldA']; ring

lemma pointwise_B (k : Fin n) (u : Fin n → ℝ) (hu : Function.Injective u) :
    huaWeight u * ((1 + 3 * u k ^ 2) + (1 + u k ^ 2) * u k * logDeriv 2 u k)
      = loopD k (fieldB k) (fieldB' k) u := by
  rw [huaWeight_eq, loopD, dWp_eq k u hu, dHn, logDeriv, fieldB, fieldB']; ring

lemma integral_hua_eq (f : (Fin n → ℝ) → ℝ) :
    ∫ u, f u ∂(huaMeasure n) = (huaZ n)⁻¹ * ∫ u, huaWeight u * f u := by
  rw [huaMeasure, integral_withDensity_eq_integral_smul measurable_huaDensity,
    ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only [NNReal.smul_def, coe_huaDensity, smul_eq_mul]; ring

/-- Loop equation (a) for the Hua ensemble with `h = 2`. -/
theorem huaMeasure_loopA : ∫ u, divA 2 u ∂(huaMeasure n) = 0 := by
  rw [integral_hua_eq]
  have e : (fun u : Fin n → ℝ => huaWeight u * divA 2 u) =ᵐ[volume]
      fun u => ∑ k, loopD k (fieldA k) (fieldA' k) u := by
    filter_upwards [ae_injective_volume] with u hu
    rw [divA, mul_sum]; exact sum_congr rfl fun k _ => pointwise_A k u hu
  have hm : ∀ k : Fin n, Measurable (fieldA k) := fun k => by unfold fieldA; fun_prop
  have hm' : ∀ k : Fin n, Measurable (fieldA' k) := fun k => by unfold fieldA'; fun_prop
  have ha : (0 : ℝ) ≤ 2 * n + 1 := by positivity
  rw [integral_congr_ae e, integral_finsetSum _ fun k _ =>
    integrable_loopD k _ _ _ (hm k) (hm' k) ha (fieldA_bound k) (fieldA'_bound k)]
  rw [sum_eq_zero fun k _ => integral_loopD k _ _ _ (hasLineDerivAt_fieldA k) (hm k) (hm' k)
    ha (fieldA_bound k) (fieldA'_bound k), mul_zero]

/-- Loop equation (b) for the Hua ensemble with `h = 2`. -/
theorem huaMeasure_loopB : ∫ u, divB 2 u ∂(huaMeasure n) = 0 := by
  rw [integral_hua_eq]
  have e : (fun u : Fin n → ℝ => huaWeight u * divB 2 u) =ᵐ[volume]
      fun u => ∑ k, loopD k (fieldB k) (fieldB' k) u := by
    filter_upwards [ae_injective_volume] with u hu
    rw [divB, mul_sum]; exact sum_congr rfl fun k _ => pointwise_B k u hu
  have hm : ∀ k : Fin n, Measurable (fieldB k) := fun k => by unfold fieldB; fun_prop
  have hm' : ∀ k : Fin n, Measurable (fieldB' k) := fun k => by unfold fieldB'; fun_prop
  have ha : (0 : ℝ) ≤ 3 := by norm_num
  rw [integral_congr_ae e, integral_finsetSum _ fun k _ =>
    integrable_loopD k _ _ _ (hm k) (hm' k) ha (fieldB_bound k) (fieldB'_bound k)]
  rw [sum_eq_zero fun k _ => integral_loopD k _ _ _ (hasLineDerivAt_fieldB k) (hm k) (hm' k)
    ha (fieldB_bound k) (fieldB'_bound k), mul_zero]

end Singh




/-!
The Cayley transform `u = cot(θ/2)` from the circle weight `|1-e^{iθ}|^4` to the Hua ensemble.
-/

open MeasureTheory Finset Real

namespace Singh

variable {n : ℕ}

/-- `θ_k = π - 2 arctan u_k`, the inverse of `u_k = cot(θ_k/2)`. -/
noncomputable def cmap (u : Fin n → ℝ) : Fin n → ℝ := fun k => π - 2 * arctan (u k)

/-- Derivative of `cmap`: the diagonal map with entries `-2/(1+u_k^2)`. -/
noncomputable def cmapD (u : Fin n → ℝ) : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
  LinearMap.toContinuousLinearMap
    (Matrix.toLin' (Matrix.diagonal fun k => -2 / (1 + u k ^ 2)))

lemma cmapD_apply (u v : Fin n → ℝ) (k : Fin n) :
    cmapD u v k = -2 / (1 + u k ^ 2) * v k := by
  show (Matrix.toLin' (Matrix.diagonal fun k => -2 / (1 + u k ^ 2))) v k = _
  rw [Matrix.toLin'_apply, Matrix.mulVec_diagonal]

lemma hasFDerivAt_cmap (u : Fin n → ℝ) : HasFDerivAt cmap (cmapD u) u := by
  rw [hasFDerivAt_pi']
  intro i
  have h := (((hasDerivAt_arctan (u i)).comp_hasFDerivAt u
    (hasFDerivAt_apply (𝕜 := ℝ) i u)).const_mul 2).const_sub π
  convert h using 1
  · funext v; simp [cmap]
  · ext v
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply, cmapD_apply,
      ContinuousLinearMap.neg_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    simp; ring

lemma det_cmapD (u : Fin n → ℝ) : |(cmapD u).det| = 2 ^ n / bigG u := by
  have : (cmapD u).det = ∏ k, (-2 / (1 + u k ^ 2)) := by
    simp [cmapD, ContinuousLinearMap.det, LinearMap.det_toLin', Matrix.det_diagonal]
  rw [this, abs_prod, bigG, div_eq_mul_inv, ← prod_inv_distrib,
    show (2 : ℝ) ^ n = ∏ _k : Fin n, (2 : ℝ) by simp, ← prod_mul_distrib]
  refine prod_congr rfl fun k _ => ?_
  rw [abs_div, abs_neg, abs_two, abs_of_pos (by positivity : (0 : ℝ) < 1 + u k ^ 2)]; ring

lemma cmap_injective : Function.Injective (cmap (n := n)) := by
  intro u v h
  funext k
  have := congrFun h k
  simp only [cmap] at this
  exact arctan_injective (by linarith)

lemma cmap_image : cmap '' Set.univ = boxC n := by
  ext θ
  simp only [Set.image_univ, Set.mem_range, boxC, Set.mem_pi, Set.mem_univ, true_implies,
    Set.mem_Ioo]
  constructor
  · rintro ⟨u, rfl⟩ k
    have := arctan_lt_pi_div_two (u k)
    have := neg_pi_div_two_lt_arctan (u k)
    simp only [cmap]; constructor <;> linarith
  · intro h
    refine ⟨fun k => tan ((π - θ k) / 2), funext fun k => ?_⟩
    obtain ⟨h1, h2⟩ := h k
    simp only [cmap]
    rw [arctan_tan (by linarith) (by linarith)]; ring

lemma half_cmap (u : Fin n → ℝ) (k : Fin n) : cmap u k / 2 = π / 2 - arctan (u k) := by
  simp only [cmap]; ring

lemma sin_half_cmap (u : Fin n → ℝ) (k : Fin n) :
    sin (cmap u k / 2) = 1 / √(1 + u k ^ 2) := by
  rw [half_cmap, sin_pi_div_two_sub, cos_arctan]

lemma cos_half_cmap (u : Fin n → ℝ) (k : Fin n) :
    cos (cmap u k / 2) = u k / √(1 + u k ^ 2) := by
  rw [half_cmap, cos_pi_div_two_sub, sin_arctan]

lemma cot_half_cmap (u : Fin n → ℝ) (k : Fin n) :
    cos (cmap u k / 2) / sin (cmap u k / 2) = u k := by
  rw [sin_half_cmap, cos_half_cmap]
  have : 0 < √(1 + u k ^ 2) := Real.sqrt_pos.mpr (by positivity)
  field_simp

lemma sin_sq_diff_cmap (u : Fin n → ℝ) (a b : Fin n) :
    sin ((cmap u a - cmap u b) / 2) ^ 2 = (u a - u b) ^ 2 / ((1 + u a ^ 2) * (1 + u b ^ 2)) := by
  have e : (cmap u a - cmap u b) / 2 = arctan (u b) - arctan (u a) := by simp only [cmap]; ring
  have ha : 0 < √(1 + u a ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have hb : 0 < √(1 + u b ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have sa := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 1 + u a ^ 2)
  have sb := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 1 + u b ^ 2)
  rw [e, sin_sub, sin_arctan, sin_arctan, cos_arctan, cos_arctan]
  field_simp
  rw [sa, sb]; ring

lemma Ssum_cmap (u : Fin n → ℝ) : Ssum (cmap u) = (∑ k, u k) / 2 := by
  simp only [Ssum, cot_half_cmap]; ring

lemma jac_wC_cmap (u : Fin n → ℝ) :
    |(cmapD u).det| * wC (cmap u) = 2 ^ n * huaWeight u := by
  have hG := bigG_pos u
  have e1 : ∏ p ∈ pairs n, sin ((cmap u p.1 - cmap u p.2) / 2) ^ 2
      = Wp u / (bigG u ^ n / bigG u) := by
    simp only [sin_sq_diff_cmap]
    rw [prod_div_distrib, pairs_prod_g, Wp]
  have e2 : ∏ k, sin (cmap u k / 2) ^ 4 = (bigG u ^ 2)⁻¹ := by
    rw [bigG, ← prod_pow, ← prod_inv_distrib]
    refine prod_congr rfl fun k _ => ?_
    rw [sin_half_cmap]
    have s := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 1 + u k ^ 2)
    rw [div_pow, show √(1 + u k ^ 2) ^ 4 = (√(1 + u k ^ 2) ^ 2) ^ 2 by ring, s]; simp
  rw [det_cmapD, wC, e1, e2, huaWeight, vdm_eq_Wp]
  field_simp
  ring

/-- Change of variables `θ = cmap u` on the box. -/
lemma integral_boxC (g : (Fin n → ℝ) → ℝ) :
    ∫ θ in boxC n, g θ = ∫ u, 2 ^ n / bigG u * g (cmap u) := by
  rw [← cmap_image, integral_image_eq_integral_abs_det_fderiv_smul (μ := volume)
    MeasurableSet.univ (fun u _ => (hasFDerivAt_cmap u).hasFDerivWithinAt)
    cmap_injective.injOn g, Measure.restrict_univ]
  simp only [det_cmapD, smul_eq_mul]

lemma jac_wC_cmap' (u : Fin n → ℝ) : 2 ^ n / bigG u * wC (cmap u) = 2 ^ n * huaWeight u := by
  rw [← det_cmapD]; exact jac_wC_cmap u

/-- **Cayley transform.** `E_{w₀}[S^2] = E_{n,2}[((∑ u)/2)^2]`. -/
theorem circleE_eq_hua (n : ℕ) :
    circleE n = ∫ u, ((∑ k, u k) / 2) ^ 2 ∂(huaMeasure n) := by
  have h1 : ∫ θ in boxC n, Ssum θ ^ 2 * wC θ
      = 2 ^ n * ∫ u : Fin n → ℝ, huaWeight u * ((∑ k, u k) / 2) ^ 2 := by
    rw [integral_boxC, ← integral_const_mul]
    congr 1; funext u
    rw [Ssum_cmap]
    calc 2 ^ n / bigG u * (((∑ k, u k) / 2) ^ 2 * wC (cmap u))
        = ((∑ k, u k) / 2) ^ 2 * (2 ^ n / bigG u * wC (cmap u)) := by ring
      _ = _ := by rw [jac_wC_cmap']; ring
  have h2 : ∫ θ in boxC n, wC θ = 2 ^ n * huaZ n := by
    rw [integral_boxC, huaZ, ← integral_const_mul]
    congr 1; funext u; exact jac_wC_cmap' u
  have hZ := (huaZ_pos (n := n)).ne'
  rw [circleE, h1, h2, integral_hua_eq]
  field_simp

lemma integral_wC_pos (n : ℕ) : 0 < ∫ θ in boxC n, wC θ := by
  rw [integral_boxC, show (fun u : Fin n → ℝ => 2 ^ n / bigG u * wC (cmap u))
    = fun u => 2 ^ n * huaWeight u from funext jac_wC_cmap', integral_const_mul]
  exact mul_pos (by positivity) huaZ_pos

end Singh





/-!
Linearization: the conditional variance of `log|Λ'(θ₁)| - log|Λ'(θ₂)|` given an adjacent
pair of eigenangles at gap `δ`, under the Weyl density, satisfies `Var/δ^2 → E_{w₀}[S^2]`.
-/

open MeasureTheory Finset Real Filter Topology

namespace Singh

variable {n : ℕ}

/-! ### Chord identities -/

lemma norm_exp_sub_exp (a b : ℝ) :
    ‖Complex.exp (Complex.I * a) - Complex.exp (Complex.I * b)‖ = 2 * |sin ((a - b) / 2)| := by
  have e : Complex.exp (Complex.I * a) - Complex.exp (Complex.I * b)
      = Complex.exp (Complex.I * b) * (Complex.exp (Complex.I * ((a - b : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, ← Complex.exp_add]; push_cast; ring_nf
  rw [e, norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul, Complex.norm_exp_I_mul_ofReal_sub_one,
    norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_two]

/-! ### Reflection `θ ↦ 2π - θ` -/

/-- The reflection `θ_k ↦ 2π - θ_k`. -/
noncomputable def refl (θ : Fin n → ℝ) : Fin n → ℝ := fun k => 2 * π - θ k

noncomputable def reflD : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
  LinearMap.toContinuousLinearMap (Matrix.toLin' (Matrix.diagonal fun _ => (-1 : ℝ)))

lemma hasFDerivAt_refl (θ : Fin n → ℝ) : HasFDerivAt refl (reflD (n := n)) θ := by
  rw [hasFDerivAt_pi']
  intro i
  have h := (hasFDerivAt_apply (𝕜 := ℝ) i θ).const_sub (2 * π)
  refine h.congr_fderiv ?_
  ext v
  show _ = (Matrix.toLin' (Matrix.diagonal fun _ => (-1 : ℝ))) v i
  rw [Matrix.toLin'_apply, Matrix.mulVec_diagonal]; simp

lemma integral_refl (g : (Fin n → ℝ) → ℝ) : ∫ θ, g (refl θ) = ∫ θ, g θ := by
  have himg : refl '' Set.univ = (Set.univ : Set (Fin n → ℝ)) := by
    refine Set.eq_univ_of_forall fun θ => ⟨refl θ, trivial, funext fun k => ?_⟩
    simp [refl]
  have hinj : Set.InjOn (refl (n := n)) Set.univ := fun x _ y _ h => by
    funext k; have := congrFun h k; simp only [refl] at this; linarith
  have hdet : |(reflD (n := n)).det| = 1 := by
    have : (reflD (n := n)).det = ∏ _k : Fin n, (-1 : ℝ) := by
      simp [reflD, ContinuousLinearMap.det, LinearMap.det_toLin', Matrix.det_diagonal]
    rw [this, abs_prod]; simp
  have := integral_image_eq_integral_abs_det_fderiv_smul (μ := volume) MeasurableSet.univ
    (fun θ _ => (hasFDerivAt_refl θ).hasFDerivWithinAt) hinj g
  rw [himg] at this
  simp only [Measure.restrict_univ] at this
  simp only [hdet, one_smul] at this
  exact this.symm

lemma fL_two_pi_sub (y : ℝ) : fL (2 * π - y) = fL y := by
  unfold fL
  rw [show (2 * π - y) / 2 = π - y / 2 by ring, sin_pi_sub]

lemma Xd_refl (δ : ℝ) (θ : Fin n → ℝ) : Xd δ (refl θ) = -Xd δ θ := by
  unfold Xd refl
  rw [← sum_neg_distrib]
  refine sum_congr rfl fun k _ => ?_
  rw [show 2 * π - θ k + δ / 2 = 2 * π - (θ k - δ / 2) by ring,
    show 2 * π - θ k - δ / 2 = 2 * π - (θ k + δ / 2) by ring, fL_two_pi_sub, fL_two_pi_sub]
  ring

lemma pwRaw_refl (δ : ℝ) (θ : Fin n → ℝ) : pwRaw δ (refl θ) = pwRaw δ θ := by
  unfold pwRaw refl
  have h1 : (∏ p ∈ pairs n, sin ((2 * π - θ p.1 - (2 * π - θ p.2)) / 2) ^ 2)
      = ∏ p ∈ pairs n, sin ((θ p.1 - θ p.2) / 2) ^ 2 := by
    refine prod_congr rfl fun p _ => ?_
    rw [show (2 * π - θ p.1 - (2 * π - θ p.2)) / 2 = -((θ p.1 - θ p.2) / 2) by ring, sin_neg,
      neg_sq]
  have h2 : (∏ k, (sin ((2 * π - θ k - δ / 2) / 2) ^ 2 * sin ((2 * π - θ k + δ / 2) / 2) ^ 2))
      = ∏ k, (sin ((θ k - δ / 2) / 2) ^ 2 * sin ((θ k + δ / 2) / 2) ^ 2) := by
    refine prod_congr rfl fun k _ => ?_
    rw [show (2 * π - θ k - δ / 2) / 2 = π - (θ k + δ / 2) / 2 by ring,
      show (2 * π - θ k + δ / 2) / 2 = π - (θ k - δ / 2) / 2 by ring, sin_pi_sub, sin_pi_sub]
    ring
  rw [h1, h2]

lemma refl_mem_boxD (δ : ℝ) (θ : Fin n → ℝ) : refl θ ∈ boxD n δ ↔ θ ∈ boxD n δ := by
  simp only [boxD, refl, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ioo]
  refine forall_congr' fun k => ?_
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

lemma pw_refl (δ : ℝ) (θ : Fin n → ℝ) : pw δ (refl θ) = pw δ θ := by
  unfold pw
  by_cases h : θ ∈ boxD n δ
  · rw [Set.indicator_of_mem ((refl_mem_boxD δ θ).mpr h), Set.indicator_of_mem h, pwRaw_refl]
  · rw [Set.indicator_of_notMem (fun h' => h ((refl_mem_boxD δ θ).mp h')),
      Set.indicator_of_notMem h]

/-- The conditional mean of `Xd` vanishes. -/
lemma integral_Xd_pw (δ : ℝ) : ∫ θ : Fin n → ℝ, Xd δ θ * pw δ θ = 0 := by
  have h := integral_refl (n := n) (fun θ => Xd δ θ * pw δ θ)
  simp only [Xd_refl, pw_refl, neg_mul, integral_neg] at h
  linarith

/-! ### The domination bound -/

lemma log_sub_mul_le {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hy : y ≤ 1) :
    (Real.log y - Real.log x) * x * y ≤ y - x := by
  have h := Real.log_le_sub_one_of_pos (div_pos (hx.trans_le hxy) hx)
  rw [Real.log_div (hx.trans_le hxy).ne' hx.ne'] at h
  have hl : 0 ≤ Real.log y - Real.log x :=
    sub_nonneg.mpr (Real.log_le_log hx hxy)
  have h2 : (Real.log y - Real.log x) * x ≤ y - x := by
    have := mul_le_mul_of_nonneg_right h hx.le
    rwa [sub_one_mul, div_mul_cancel₀ _ hx.ne'] at this
  calc (Real.log y - Real.log x) * x * y ≤ (Real.log y - Real.log x) * x * 1 :=
        mul_le_mul_of_nonneg_left hy (mul_nonneg hl hx.le)
    _ ≤ y - x := by rw [mul_one]; exact h2

lemma abs_log_sub_mul_le {x y : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) (hy : 0 < y) (hy1 : y ≤ 1) :
    |Real.log y - Real.log x| * x * y ≤ |y - x| := by
  rcases le_total x y with h | h
  · rw [abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log hx h)), abs_of_nonneg (sub_nonneg.mpr h)]
    exact log_sub_mul_le hx h hy1
  · rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log hy h)), abs_sub_comm,
      abs_of_nonneg (sub_nonneg.mpr h), mul_right_comm]
    exact log_sub_mul_le hy h hx1

lemma sin_half_pos {x : ℝ} (h0 : 0 < x) (h1 : x < 2 * π) : 0 < sin (x / 2) :=
  sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)

/-- Per-angle bound: `|t_k| sin a sin b ≤ δ/2`. -/
lemma term_bound {δ x : ℝ} (hδ : 0 ≤ δ) (h1 : δ / 2 < x) (h2 : x < 2 * π - δ / 2) :
    |fL (x + δ / 2) - fL (x - δ / 2)| * (sin ((x - δ / 2) / 2) * sin ((x + δ / 2) / 2))
      ≤ δ / 2 := by
  have ha := sin_half_pos (x := x - δ / 2) (by linarith) (by linarith)
  have hb := sin_half_pos (x := x + δ / 2) (by linarith) (by linarith)
  have := abs_log_sub_mul_le ha (sin_le_one _) hb (sin_le_one _)
  rw [← mul_assoc]
  refine this.trans ((Real.abs_sin_sub_sin_le _ _).trans (le_of_eq ?_))
  rw [show (x + δ / 2) / 2 - (x - δ / 2) / 2 = δ / 2 by ring, abs_of_nonneg (by linarith)]

lemma pairs_prod_nonneg_le_one (θ : Fin n → ℝ) :
    0 ≤ (∏ p ∈ pairs n, sin ((θ p.1 - θ p.2) / 2) ^ 2) ∧
      (∏ p ∈ pairs n, sin ((θ p.1 - θ p.2) / 2) ^ 2) ≤ 1 :=
  ⟨prod_nonneg fun _ _ => sq_nonneg _,
    Finset.prod_le_one (fun _ _ => sq_nonneg _) fun _ _ => by
      rw [sq_le_one_iff_abs_le_one]; exact abs_sin_le_one _⟩

lemma pwRaw_nonneg_le_one (δ : ℝ) (θ : Fin n → ℝ) : 0 ≤ pwRaw δ θ ∧ pwRaw δ θ ≤ 1 := by
  have hs : ∀ y : ℝ, 0 ≤ sin y ^ 2 ∧ sin y ^ 2 ≤ 1 := fun y =>
    ⟨sq_nonneg _, by rw [sq_le_one_iff_abs_le_one]; exact abs_sin_le_one _⟩
  have hq : 0 ≤ ∏ k, (sin ((θ k - δ / 2) / 2) ^ 2 * sin ((θ k + δ / 2) / 2) ^ 2) ∧
      ∏ k, (sin ((θ k - δ / 2) / 2) ^ 2 * sin ((θ k + δ / 2) / 2) ^ 2) ≤ 1 :=
    ⟨prod_nonneg fun k _ => mul_nonneg (hs _).1 (hs _).1,
      Finset.prod_le_one (fun k _ => mul_nonneg (hs _).1 (hs _).1) fun k _ =>
        mul_le_one₀ (hs _).2 (hs _).1 (hs _).2⟩
  obtain ⟨p0, p1⟩ := pairs_prod_nonneg_le_one θ
  exact ⟨mul_nonneg p0 hq.1, mul_le_one₀ p1 hq.1 hq.2⟩

lemma boxD_subset {δ : ℝ} (hδ : 0 ≤ δ) : boxD n δ ⊆ boxC n := by
  intro θ h
  simp only [boxD, boxC, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ioo] at h ⊢
  exact fun k => ⟨by linarith [(h k).1], by linarith [(h k).2]⟩

/-- Domination: `(Xd/δ)^2 · pw ≤ n^2/4` on `boxC`, and `0` off it. -/
lemma F_bound {δ : ℝ} (hδ : 0 < δ) (θ : Fin n → ℝ) :
    ‖(Xd δ θ / δ) ^ 2 * pw δ θ‖ ≤ (boxC n).indicator (fun _ => (n : ℝ) ^ 2 / 4) θ := by
  unfold pw
  by_cases h : θ ∈ boxD n δ
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem (boxD_subset hδ.le h)]
    have hm : ∀ k, δ / 2 < θ k ∧ θ k < 2 * π - δ / 2 := by
      intro k; simpa [boxD] using h k
    set t : Fin n → ℝ := fun k => fL (θ k + δ / 2) - fL (θ k - δ / 2)
    set s : Fin n → ℝ := fun k => sin ((θ k - δ / 2) / 2) * sin ((θ k + δ / 2) / 2)
    have hs0 : ∀ k, 0 ≤ s k := fun k =>
      mul_nonneg (sin_half_pos (by linarith [(hm k).1]) (by linarith [(hm k).2])).le
        (sin_half_pos (by linarith [(hm k).1]) (by linarith [(hm k).2])).le
    have hs1 : ∀ k, s k ≤ 1 := fun k =>
      mul_le_one₀ (sin_le_one _)
        (sin_half_pos (x := θ k + δ / 2) (by linarith [(hm k).1]) (by linarith [(hm k).2])).le
        (sin_le_one _)
    have hts : ∀ k, |t k| * s k ≤ δ / 2 := fun k => term_bound hδ.le (hm k).1 (hm k).2
    have hQ : ∏ k, (sin ((θ k - δ / 2) / 2) ^ 2 * sin ((θ k + δ / 2) / 2) ^ 2)
        = ∏ k, s k ^ 2 := prod_congr rfl fun k _ => by simp only [s]; ring
    have hP : ∀ j, ∏ k, s k ^ 2 ≤ s j ^ 2 := by
      intro j
      rw [← mul_prod_erase _ _ (mem_univ j)]
      refine mul_le_of_le_one_right (sq_nonneg _) (Finset.prod_le_one (fun _ _ => sq_nonneg _)
        fun k _ => ?_)
      exact pow_le_one₀ (hs0 k) (hs1 k)
    have hQ0 : 0 ≤ ∏ k, s k ^ 2 := prod_nonneg fun _ _ => sq_nonneg _
    obtain ⟨p0, p1⟩ := pairs_prod_nonneg_le_one θ
    have hX : Xd δ θ = ∑ k, t k := rfl
    have hCS : (∑ k, t k) ^ 2 ≤ n * ∑ k, t k ^ 2 := by
      simpa using sq_sum_le_card_mul_sum_sq (s := (univ : Finset (Fin n))) (f := t)
    have hterm : ∀ j, t j ^ 2 * ∏ k, s k ^ 2 ≤ (δ / 2) ^ 2 := by
      intro j
      calc t j ^ 2 * ∏ k, s k ^ 2 ≤ t j ^ 2 * s j ^ 2 :=
            mul_le_mul_of_nonneg_left (hP j) (sq_nonneg _)
        _ = (|t j| * s j) ^ 2 := by rw [mul_pow (|t j|), sq_abs]
        _ ≤ (δ / 2) ^ 2 :=
            pow_le_pow_left₀ (mul_nonneg (abs_nonneg _) (hs0 j)) (hts j) 2
    have hmain : (∑ k, t k) ^ 2 * ∏ k, s k ^ 2 ≤ (n : ℝ) ^ 2 * (δ / 2) ^ 2 := by
      calc (∑ k, t k) ^ 2 * ∏ k, s k ^ 2 ≤ (n * ∑ k, t k ^ 2) * ∏ k, s k ^ 2 :=
            mul_le_mul_of_nonneg_right hCS hQ0
        _ = n * ∑ j, t j ^ 2 * ∏ k, s k ^ 2 := by rw [mul_assoc, sum_mul]
        _ ≤ n * ∑ _j : Fin n, (δ / 2) ^ 2 :=
            mul_le_mul_of_nonneg_left (sum_le_sum fun j _ => hterm j) (Nat.cast_nonneg _)
        _ = (n : ℝ) ^ 2 * (δ / 2) ^ 2 := by simp; ring
    have hpw0 := (pwRaw_nonneg_le_one δ θ).1
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) hpw0), pwRaw, hQ, hX,
      div_pow]
    have hδ2 : 0 < δ ^ 2 := by positivity
    rw [div_mul_eq_mul_div, div_le_iff₀ hδ2]
    calc (∑ k, t k) ^ 2 * ((∏ p ∈ pairs n, sin ((θ p.1 - θ p.2) / 2) ^ 2) * ∏ k, s k ^ 2)
        ≤ (∑ k, t k) ^ 2 * (1 * ∏ k, s k ^ 2) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right p1 hQ0) (sq_nonneg _)
      _ ≤ (n : ℝ) ^ 2 * (δ / 2) ^ 2 := by rw [one_mul]; exact hmain
      _ = (n : ℝ) ^ 2 / 4 * δ ^ 2 := by ring
  · rw [Set.indicator_of_notMem h, mul_zero, norm_zero]
    exact Set.indicator_nonneg (fun _ _ => by positivity) _

/-! ### Pointwise limits -/

lemma hasDerivAt_fL {x : ℝ} (h0 : 0 < x) (h1 : x < 2 * π) :
    HasDerivAt fL (cos (x / 2) * (1 / 2) / sin (x / 2)) x := by
  have h := ((hasDerivAt_id x).div_const 2).sin
  simp only [id] at h
  exact h.log (sin_half_pos h0 h1).ne'

lemma tendsto_half_ne (c : ℝ) (hc : c ≠ 0) :
    Tendsto (fun δ : ℝ => c * δ) (𝓝[>] 0) (𝓝[≠] 0) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
  · have : Tendsto (fun δ : ℝ => c * δ) (𝓝 0) (𝓝 (c * 0)) :=
      (continuous_const.mul continuous_id).tendsto 0
    rw [mul_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact mul_ne_zero hc (ne_of_gt hδ)

/-- The symmetric difference quotient converges to the derivative. -/
lemma tendsto_sym_quot {f : ℝ → ℝ} {d x : ℝ} (hf : HasDerivAt f d x) :
    Tendsto (fun δ => (f (x + δ / 2) - f (x - δ / 2)) / δ) (𝓝[>] 0) (𝓝 d) := by
  have hs := hasDerivAt_iff_tendsto_slope_zero.mp hf
  have h1 := hs.comp (tendsto_half_ne (1 / 2) (by norm_num))
  have h2 := hs.comp (tendsto_half_ne (-1 / 2) (by norm_num))
  have h3 := (h1.add h2).div_const 2
  rw [show (d + d) / 2 = d by ring] at h3
  refine h3.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  have hδ0 : δ ≠ 0 := ne_of_gt hδ
  simp only [Function.comp, smul_eq_mul]
  rw [show x + -1 / 2 * δ = x - δ / 2 by ring, show x + 1 / 2 * δ = x + δ / 2 by ring]
  field_simp
  ring

lemma eventually_mem_boxD {θ : Fin n → ℝ} (h : θ ∈ boxC n) :
    ∀ᶠ δ in 𝓝[>] (0 : ℝ), θ ∈ boxD n δ := by
  have hm : ∀ k, 0 < θ k ∧ θ k < 2 * π := by intro k; simpa [boxC] using h k
  have : ∀ k, ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ / 2 < θ k ∧ θ k < 2 * π - δ / 2 := by
    intro k
    have ha : ∀ᶠ δ in 𝓝 (0 : ℝ), δ < 2 * θ k := eventually_lt_nhds (by linarith [(hm k).1])
    have hb : ∀ᶠ δ in 𝓝 (0 : ℝ), δ < 2 * (2 * π - θ k) :=
      eventually_lt_nhds (by linarith [(hm k).2])
    filter_upwards [nhdsWithin_le_nhds ha, nhdsWithin_le_nhds hb] with δ h1 h2
    exact ⟨by linarith, by linarith⟩
  filter_upwards [Filter.eventually_all.mpr this] with δ hδ
  simpa [boxD] using hδ

lemma continuous_pwRaw (θ : Fin n → ℝ) : Continuous fun δ => pwRaw δ θ := by
  unfold pwRaw; fun_prop

lemma pwRaw_zero (θ : Fin n → ℝ) : pwRaw 0 θ = wC θ := by
  unfold pwRaw wC
  rw [prod_congr rfl (fun k _ => show sin ((θ k - 0 / 2) / 2) ^ 2 * sin ((θ k + 0 / 2) / 2) ^ 2
    = sin (θ k / 2) ^ 4 by simp only [zero_div, sub_zero, add_zero]; ring)]

lemma Xd_div_tendsto {θ : Fin n → ℝ} (h : θ ∈ boxC n) :
    Tendsto (fun δ => Xd δ θ / δ) (𝓝[>] 0) (𝓝 (Ssum θ)) := by
  have hm : ∀ k, 0 < θ k ∧ θ k < 2 * π := by intro k; simpa [boxC] using h k
  have hS : Ssum θ = ∑ k, cos (θ k / 2) * (1 / 2) / sin (θ k / 2) := by
    rw [Ssum, mul_sum]; refine sum_congr rfl fun k _ => ?_; ring
  rw [hS]
  have : (fun δ => Xd δ θ / δ)
      = fun δ => ∑ k, (fL (θ k + δ / 2) - fL (θ k - δ / 2)) / δ := by
    funext δ; rw [Xd, sum_div]
  rw [this]
  exact tendsto_finsetSum _ fun k _ => tendsto_sym_quot (hasDerivAt_fL (hm k).1 (hm k).2)

lemma pw_tendsto (θ : Fin n → ℝ) :
    Tendsto (fun δ => pw δ θ) (𝓝[>] 0) (𝓝 ((boxC n).indicator wC θ)) := by
  by_cases h : θ ∈ boxC n
  · rw [Set.indicator_of_mem h, ← pwRaw_zero]
    have hc := ((continuous_pwRaw θ).tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
    refine hc.congr' ?_
    filter_upwards [eventually_mem_boxD h] with δ hδ
    rw [pw, Set.indicator_of_mem hδ]
  · rw [Set.indicator_of_notMem h]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    rw [pw, Set.indicator_of_notMem (fun h' => h (boxD_subset (le_of_lt hδ) h'))]

lemma F_tendsto (θ : Fin n → ℝ) :
    Tendsto (fun δ => (Xd δ θ / δ) ^ 2 * pw δ θ) (𝓝[>] 0)
      (𝓝 ((boxC n).indicator (fun θ => Ssum θ ^ 2 * wC θ) θ)) := by
  by_cases h : θ ∈ boxC n
  · have hp := pw_tendsto θ
    rw [Set.indicator_of_mem h] at hp ⊢
    exact ((Xd_div_tendsto h).pow 2).mul hp
  · rw [Set.indicator_of_notMem h]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    rw [pw, Set.indicator_of_notMem (fun h' => h (boxD_subset (le_of_lt hδ) h')), mul_zero]

/-! ### Dominated convergence -/

lemma measurableSet_boxD (δ : ℝ) : MeasurableSet (boxD n δ) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Ioo

lemma measurableSet_boxC : MeasurableSet (boxC n) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Ioo

lemma measurable_pw (δ : ℝ) : Measurable (pw (n := n) δ) := by
  unfold pw
  refine Measurable.indicator ?_ (measurableSet_boxD δ)
  unfold pwRaw; fun_prop

lemma measurable_Xd (δ : ℝ) : Measurable (Xd (n := n) δ) := by
  unfold Xd fL; fun_prop

lemma volume_boxC_ne_top : volume (boxC n) ≠ ⊤ := by
  rw [boxC, volume_pi_pi]; simp [Real.volume_Ioo, ENNReal.mul_eq_top]

lemma integrable_indicator_const (c : ℝ) :
    Integrable ((boxC n).indicator fun _ => c) := by
  rw [integrable_indicator_iff measurableSet_boxC]
  exact integrableOn_const volume_boxC_ne_top

lemma integral_F_tendsto :
    Tendsto (fun δ => ∫ θ : Fin n → ℝ, (Xd δ θ / δ) ^ 2 * pw δ θ) (𝓝[>] 0)
      (𝓝 (∫ θ in boxC n, Ssum θ ^ 2 * wC θ)) := by
  rw [← integral_indicator measurableSet_boxC]
  refine tendsto_integral_filter_of_dominated_convergence
    ((boxC n).indicator fun _ => (n : ℝ) ^ 2 / 4) ?_ ?_ (integrable_indicator_const _)
    (Eventually.of_forall F_tendsto)
  · exact Eventually.of_forall fun δ =>
      (((measurable_Xd δ).div_const δ).pow_const 2 |>.mul (measurable_pw δ)).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact Eventually.of_forall (F_bound hδ)

lemma integral_pw_tendsto :
    Tendsto (fun δ => ∫ θ : Fin n → ℝ, pw δ θ) (𝓝[>] 0) (𝓝 (∫ θ in boxC n, wC θ)) := by
  rw [← integral_indicator measurableSet_boxC]
  refine tendsto_integral_filter_of_dominated_convergence
    ((boxC n).indicator fun _ => (1 : ℝ)) ?_ ?_ (integrable_indicator_const _)
    (Eventually.of_forall pw_tendsto)
  · exact Eventually.of_forall fun δ => (measurable_pw δ).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with δ hδ
    refine Eventually.of_forall fun θ => ?_
    unfold pw
    by_cases h : θ ∈ boxD n δ
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem (boxD_subset (le_of_lt hδ) h),
        Real.norm_eq_abs, abs_of_nonneg (pwRaw_nonneg_le_one δ θ).1]
      exact (pwRaw_nonneg_le_one δ θ).2
    · rw [Set.indicator_of_notMem h, norm_zero]
      exact Set.indicator_nonneg (fun _ _ => zero_le_one) _

/-- **Linearization.** `Var(X_δ | adjacent pair at gap δ) / δ^2 → E_{w₀}[S^2]`. -/
theorem palmVar_tendsto (n : ℕ) :
    Tendsto (fun δ => palmVar n δ / δ ^ 2) (𝓝[>] 0) (𝓝 (circleE n)) := by
  have h := (integral_F_tendsto (n := n)).div (integral_pw_tendsto (n := n))
    (integral_wC_pos n).ne'
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  have hδ2 : δ ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hδ)
  rw [palmVar, integral_Xd_pw, zero_div, sq (0 : ℝ), mul_zero, sub_zero]
  have : (fun θ : Fin n → ℝ => (Xd δ θ / δ) ^ 2 * pw δ θ)
      = fun θ => (δ ^ 2)⁻¹ * (Xd δ θ ^ 2 * pw δ θ) := by
    funext θ; rw [div_pow]; field_simp
  simp only [Pi.div_apply]
  rw [this, integral_const_mul]
  field_simp

end Singh





/-!
# Singh Theorem: analytic statement

For `U ∈ U(N)` Haar distributed, adjacent eigenangles `θ₁ < θ₂` with normalized gap
`s = N(θ₂-θ₁)/(2π)`, and `x - y = log|Λ'(θ₁)| - log|Λ'(θ₂)|`,
`Var(x - y | s) = c_N s^2 (1 + o(1))` as `s → 0`, with `c_N = (π^2/15)(1 - 4/N^2)`.

The analytic inputs are recorded as named fields of `CUEPairData`:
* `linearization`: conditioning on the pair via the Weyl integration formula and the
  Taylor linearization, giving `Var(x-y|s)/s^2 → (2π/N)^2 E_{w₀}[S^2]`;
The Cayley transform `u = cot(θ/2)` identifying `E_{w₀}[S^2] = circleE (N-2)` with the
Hua ensemble moment `E_{n,2}[(∑u/2)^2]` is `circleE_eq_hua` in `Singh.Cayley`.
The loop equations `huaMeasure_loopA`, `huaMeasure_loopB` are proved in `Singh.Loop`
by integration by parts. The Hua measure `huaMeasure` is defined explicitly by its density; its normalization,
absolute continuity and the needed integrability are proved in `Singh.Hua`.
The linearization is proved in `Singh.Linear` (`palmVar_tendsto`) for the conditional
variance `palmVar` under the Weyl density of the remaining `N-2` angles given an adjacent
pair at gap `2πs/N`; `cuePairData` supplies it, and `theorem_cN_CUE` is the resulting
statement with no remaining inputs.
-/

open MeasureTheory Filter Topology Finset

namespace Singh

variable {n : ℕ}

/-- Second moment of `∑ u_k` in the Hua ensemble from the two loop equations. -/
theorem hua_second_moment (μ : Measure (Fin n → ℝ)) [IsProbabilityMeasure μ]
    (h : ℝ) (hh : 4 * h ^ 2 - 1 ≠ 0)
    (hinj : ∀ᵐ u ∂μ, Function.Injective u)
    (hF : Integrable (fun u : Fin n → ℝ => (∑ k, u k) ^ 2) μ)
    (hQ : Integrable (fun u : Fin n → ℝ => ∑ k, u k ^ 2) μ)
    (hA : ∫ u, divA h u ∂μ = 0) (hB : ∫ u, divB h u ∂μ = 0) :
    ∫ u, (∑ k, u k) ^ 2 ∂μ = (n : ℝ) * ((n : ℝ) + 2 * h) / (4 * h ^ 2 - 1) := by
  have eA : ∫ u, divA h u ∂μ
      = ∫ u, ((n : ℝ) + ∑ k, u k ^ 2 - 2 * h * (∑ k, u k) ^ 2) ∂μ :=
    integral_congr_ae (hinj.mono fun u hu => divA_eq h u hu)
  have eB : ∫ u, divB h u ∂μ
      = ∫ u, ((n : ℝ) ^ 2 - 2 * h * ∑ k, u k ^ 2 + (∑ k, u k) ^ 2) ∂μ :=
    integral_congr_ae (hinj.mono fun u hu => divB_eq h u hu)
  have c1 : Integrable (fun _ : Fin n → ℝ => (n : ℝ)) μ := integrable_const _
  have c2 : Integrable (fun _ : Fin n → ℝ => (n : ℝ) ^ 2) μ := integrable_const _
  have iA : Integrable (fun u : Fin n → ℝ => (n : ℝ) + ∑ k, u k ^ 2) μ := c1.add hQ
  have iF : Integrable (fun u : Fin n → ℝ => 2 * h * (∑ k, u k) ^ 2) μ := hF.const_mul _
  have iQ : Integrable (fun u : Fin n → ℝ => 2 * h * ∑ k, u k ^ 2) μ := hQ.const_mul _
  have iB : Integrable (fun u : Fin n → ℝ => (n : ℝ) ^ 2 - 2 * h * ∑ k, u k ^ 2) μ :=
    c2.sub iQ
  rw [eA, integral_sub iA iF, integral_add c1 hQ, integral_const_mul, integral_const] at hA
  rw [eB, integral_add iB hF, integral_sub c2 iQ, integral_const_mul, integral_const] at hB
  simp only [probReal_univ, smul_eq_mul, one_mul] at hA hB
  exact loop_solution _ _ _ _ hh (by linarith) hB

/-- `E_{n,2}[(∑u)^2] = n(n+4)/15` for the Hua ensemble. -/
theorem huaMeasure_second_moment (n : ℕ) :
    ∫ u, (∑ k, u k) ^ 2 ∂(huaMeasure n) = (n : ℝ) * ((n : ℝ) + 4) / 15 := by
  have := hua_second_moment (huaMeasure n) 2 (by norm_num) huaMeasure_ae_injective
    huaMeasure_int_sq_sum huaMeasure_int_sum_sq huaMeasure_loopA huaMeasure_loopB
  rw [this]; ring

/-- Analytic inputs for the CUE close-pair problem at matrix size `N`. -/
structure CUEPairData (N : ℕ) where
  /-- `V s = Var(log|Λ'(θ₁)| - log|Λ'(θ₂)| | s)`. -/
  V : ℝ → ℝ
  linearization :
    Tendsto (fun s => V s / s ^ 2) (𝓝[>] 0) (𝓝 ((2 * Real.pi / N) ^ 2 * circleE (N - 2)))

/-- `E_{w₀}[S^2] = (N^2-4)/60`. -/
theorem Ew0_eq {N : ℕ} (hN : 2 ≤ N) :
    circleE (N - 2) = ((N : ℝ) ^ 2 - 4) / 60 := by
  have hm := huaMeasure_second_moment (N - 2)
  have hc : ((N - 2 : ℕ) : ℝ) = (N : ℝ) - 2 := by
    rw [Nat.cast_sub hN]; norm_num
  rw [circleE_eq_hua]
  have : (fun u : Fin (N - 2) → ℝ => ((∑ k, u k) / 2) ^ 2)
      = fun u => (1 / 4 : ℝ) * (∑ k, u k) ^ 2 := by
    funext u; ring
  rw [this, integral_const_mul, hm, hc]
  ring

/-- **Singh Theorem.** `Var(x - y | s) / s^2 → c_N = (π^2/15)(1 - 4/N^2)` as `s → 0⁺`. -/
theorem theorem_cN {N : ℕ} (hN : 2 ≤ N) (D : CUEPairData N) :
    Tendsto (fun s => D.V s / s ^ 2) (𝓝[>] 0) (𝓝 (cN N)) := by
  have hN0 : (N : ℝ) ≠ 0 := by
    have : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    exact this.ne'
  have h := D.linearization
  rwa [Ew0_eq hN, cN_closed_form _ hN0] at h

/-- **Singh Theorem**, little-o form: `Var(x - y | s) = c_N s^2 + o(s^2)`. -/
theorem theorem_cN_isLittleO {N : ℕ} (hN : 2 ≤ N) (D : CUEPairData N) :
    (fun s => D.V s - cN N * s ^ 2) =o[𝓝[>] 0] (fun s => s ^ 2) := by
  have ht := theorem_cN hN D
  rw [Asymptotics.isLittleO_iff_tendsto']
  · have : (fun s => (D.V s - cN N * s ^ 2) / s ^ 2) =ᶠ[𝓝[>] 0]
        fun s => D.V s / s ^ 2 - cN N := by
      filter_upwards [self_mem_nhdsWithin] with s hs
      have : s ^ 2 ≠ 0 := pow_ne_zero _ (ne_of_gt hs)
      rw [sub_div, mul_div_assoc, div_self this, mul_one]
    rw [tendsto_congr' this]
    simpa using ht.sub_const (cN N)
  · filter_upwards [self_mem_nhdsWithin] with s hs h0
    exact absurd h0 (pow_ne_zero _ (ne_of_gt hs))

theorem cueV_linearization {N : ℕ} (hN : 0 < N) :
    Tendsto (fun s => cueV N s / s ^ 2) (𝓝[>] 0)
      (𝓝 ((2 * Real.pi / N) ^ 2 * circleE (N - 2))) := by
  have hc : 0 < 2 * Real.pi / N := by
    have : (0 : ℝ) < N := by exact_mod_cast hN
    positivity
  have hg : Tendsto (fun s : ℝ => 2 * Real.pi / N * s) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have : Tendsto (fun s : ℝ => 2 * Real.pi / N * s) (𝓝 0) (𝓝 (2 * Real.pi / N * 0)) :=
        (continuous_const.mul continuous_id).tendsto 0
      rw [mul_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      exact mul_pos hc hs
  have h := ((palmVar_tendsto (N - 2)).comp hg).const_mul ((2 * Real.pi / N) ^ 2)
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs0 : s ≠ 0 := ne_of_gt hs
  simp only [Function.comp, cueV]
  field_simp

/-- The analytic input, supplied by `Singh.Linear`. -/
noncomputable def cuePairData {N : ℕ} (hN : 0 < N) : CUEPairData N where
  V := cueV N
  linearization := cueV_linearization hN

/-- **Singh Theorem**: `Var(log|Λ'(θ₁)| - log|Λ'(θ₂)| | s) / s^2 → c_N` as `s → 0⁺`. -/
theorem theorem_cN_CUE {N : ℕ} (hN : 2 ≤ N) :
    Tendsto (fun s => cueV N s / s ^ 2) (𝓝[>] 0) (𝓝 (cN N)) :=
  theorem_cN hN (cuePairData (by omega))

/-- **Singh Theorem**, little-o form: `Var(x - y | s) = c_N s^2 + o(s^2)`. -/
theorem theorem_cN_CUE_isLittleO {N : ℕ} (hN : 2 ≤ N) :
    (fun s => cueV N s - cN N * s ^ 2) =o[𝓝[>] 0] (fun s => s ^ 2) :=
  theorem_cN_isLittleO hN (cuePairData (by omega))

end Singh


open MeasureTheory Filter Topology Singh

theorem solution (n : ℕ) :
    ∫ u, (∑ k, u k) ^ 2 ∂(huaMeasure n) = (n : ℝ) * ((n : ℝ) + 4) / 15 :=
  Singh.huaMeasure_second_moment n

