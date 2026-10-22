-- Prove2me | solution 1 for WFMFG.Conv.lemma_4_5
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T18:48:38.699239+00:00
-- url     : https://prove2.me/submissions/0ccdabef-2ab5-4bed-90b1-29a5d1328a18

import Mathlib
import Definitions.Def_WFMFG_Conv_Simplex
import Definitions.Def_WFMFG_Conv_Multinomial
import Definitions.Def_WFMFG_Conv_Setting

open Finset WFMFG.Conv


namespace WFMFGmult

lemma antidiag_eq (d N : ℕ) :
    Finset.Nat.antidiagonalTuple d N = (Finset.univ : Finset (Fin d)).piAntidiag N := by
  ext k; simp [Finset.mem_piAntidiag, Finset.Nat.mem_antidiagonalTuple]

lemma multW_sum (d N : ℕ) (p : Fin d → ℝ) :
    ∑ k ∈ Finset.Nat.antidiagonalTuple d N, multW p k = (∑ i, p i) ^ N := by
  rw [Finset.sum_pow_eq_sum_piAntidiag, antidiag_eq]
  rfl

lemma multW_mean (d N : ℕ) (p : Fin d → ℝ) (i : Fin d) :
    ∑ k ∈ Finset.Nat.antidiagonalTuple d N, multW p k * (k i : ℝ)
      = N * p i * (∑ j, p j) ^ (N - 1) := by
  have key : ∀ s : ℝ, (∑ j, p j + (s - 1) * p i) ^ N
      = ∑ k ∈ Finset.Nat.antidiagonalTuple d N, multW p k * s ^ (k i) := by
    intro s
    set q : Fin d → ℝ := fun j => if j = i then s * p j else p j with hq
    have hsum : ∑ j, q j = ∑ j, p j + (s - 1) * p i := by
      have : ∀ j, q j = p j + (if j = i then (s - 1) * p j else 0) := by
        intro j; simp only [hq]; split_ifs <;> ring
      simp only [this, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [← hsum, Finset.sum_pow_eq_sum_piAntidiag, ← antidiag_eq]
    apply Finset.sum_congr rfl
    intro k _
    have hprod : ∏ j, q j ^ k j = (∏ j, p j ^ k j) * s ^ (k i) := by
      have : ∀ j, q j ^ k j = p j ^ k j * (if j = i then s ^ (k j) else 1) := by
        intro j; simp only [hq]; split_ifs with h
        · rw [mul_pow, mul_comm]
        · ring
      simp only [this, Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.mem_univ, if_true]
    rw [hprod]; unfold multW; ring
  have hL : HasDerivAt (fun s : ℝ => (∑ j, p j + (s - 1) * p i) ^ N)
      ((N : ℝ) * (∑ j, p j + (1 - 1) * p i) ^ (N - 1) * p i) 1 := by
    have h1 : HasDerivAt (fun s : ℝ => ∑ j, p j + (s - 1) * p i) (p i) 1 := by
      simpa using (((hasDerivAt_id (1:ℝ)).sub_const 1).mul_const (p i)).const_add (∑ j, p j)
    simpa using h1.fun_pow N
  have hR : HasDerivAt (fun s : ℝ => ∑ k ∈ Finset.Nat.antidiagonalTuple d N, multW p k * s ^ (k i))
      (∑ k ∈ Finset.Nat.antidiagonalTuple d N, multW p k * ((k i : ℝ) * 1 ^ (k i - 1))) 1 := by
    apply HasDerivAt.fun_sum
    intro k _
    exact (hasDerivAt_pow (k i) (1:ℝ)).const_mul (multW p k)
  have hfun : (fun s : ℝ => (∑ j, p j + (s - 1) * p i) ^ N)
      = (fun s : ℝ => ∑ k ∈ Finset.Nat.antidiagonalTuple d N, multW p k * s ^ (k i)) := funext key
  rw [hfun] at hL
  have := hL.unique hR
  simp only [one_pow, mul_one, sub_self, zero_mul, add_zero] at this
  rw [← this]; ring

end WFMFGmult

namespace WFMFG32

lemma empQ_nonneg {d N : ℕ} (x : Fin N → Fin d) (y : Fin N → ℚ) (hy : y ∈ Yset N) (i : Fin d) :
    0 ≤ empQ x y i := by
  unfold empQ
  apply mul_nonneg (by positivity)
  apply Finset.sum_nonneg; intro l _; split_ifs <;> simp [hy.1 l]

lemma empQ_sum {d N : ℕ} (hN : 1 ≤ N) (x : Fin N → Fin d) (y : Fin N → ℚ) (hy : y ∈ Yset N) :
    ∑ i, empQ x y i = 1 := by
  unfold empQ
  rw [← Finset.mul_sum, Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [hy.2]
  have hN' : (N:ℚ) ≠ 0 := by positivity
  field_simp

lemma emp_std {d N : ℕ} (hN : 1 ≤ N) (x : Fin N → Fin d) (y : Fin N → ℚ) (hy : y ∈ Yset N) :
    empMeas x y ∈ stdSimplex ℝ (Fin d) := by
  refine ⟨fun i => ?_, ?_⟩
  · simp only [empMeas]; exact_mod_cast empQ_nonneg x y hy i
  · simp only [empMeas]; exact_mod_cast empQ_sum hN x y hy

lemma ratio_cast {d N : ℕ} (x : Fin N → Fin d) (y : Fin N → ℚ) (k : Fin d → ℕ) (l : Fin N) :
    ((ratioQ x y k l : ℚ) : ℝ) =
      if empQ x y (x l) = 0 then 1 else (k (x l) : ℝ) / (N * empMeas x y (x l)) := by
  unfold ratioQ empMeas; split_ifs <;> push_cast <;> rfl

lemma ratioQ_nonneg {d N : ℕ} (x : Fin N → Fin d) (y : Fin N → ℚ) (hy : y ∈ Yset N)
    (k : Fin d → ℕ) (l : Fin N) : 0 ≤ ratioQ x y k l := by
  unfold ratioQ
  split_ifs
  · norm_num
  · have := empQ_nonneg x y hy (x l); positivity

/-- total mass of the common-noise jump kernel is one. -/
lemma noise_mass {d N : ℕ} (hN : 1 ≤ N) (x : Fin N → Fin d) (y : Fin N → ℚ) (hy : y ∈ Yset N)
    (l : Fin N) :
    ∑ k ∈ Finset.Nat.antidiagonalTuple d N, multW (empMeas x y) k * (ratioQ x y k l : ℝ) = 1 := by
  have hs : ∑ i, empMeas x y i = 1 := (emp_std hN x y hy).2
  simp_rw [ratio_cast]
  split_ifs with h0
  · simp only [mul_one]; rw [WFMFGmult.multW_sum, hs, one_pow]
  · have hμ : empMeas x y (x l) ≠ 0 := by
      simp only [empMeas]; exact_mod_cast h0
    have hNr : (N:ℝ) ≠ 0 := by have : (0:ℝ) < N := by exact_mod_cast hN
                               exact this.ne'
    simp_rw [mul_div_assoc', ← Finset.sum_div]
    rw [WFMFGmult.multW_mean, hs, one_pow, mul_one]
    field_simp

lemma multW_nonneg {d : ℕ} (p : Fin d → ℝ) (hp : ∀ i, 0 ≤ p i) (k : Fin d → ℕ) :
    0 ≤ multW p k := by
  unfold multW
  apply mul_nonneg (by positivity)
  exact Finset.prod_nonneg (fun i _ => pow_nonneg (hp i) _)

lemma reweight_mem {d N : ℕ} (hN : 1 ≤ N) (x : Fin N → Fin d) (y : Fin N → ℚ) (hy : y ∈ Yset N)
    (k : Fin d → ℕ) (hk : k ∈ Finset.Nat.antidiagonalTuple d N)
    (hw : multW (empMeas x y) k ≠ 0) : reweight x y k ∈ Yset N := by
  refine ⟨fun l => mul_nonneg (hy.1 l) (ratioQ_nonneg x y hy k l), ?_⟩
  -- support condition
  have hsupp : ∀ i, empQ x y i = 0 → k i = 0 := by
    intro i hi
    by_contra hki
    apply hw
    unfold multW
    have : ∏ j, empMeas x y j ^ k j = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      have : empMeas x y i = 0 := by simp only [empMeas]; exact_mod_cast hi
      rw [this]; exact zero_pow hki
    rw [this, mul_zero]
  set r : Fin d → ℚ := fun i => if empQ x y i = 0 then 1 else (k i : ℚ) / (N * empQ x y i) with hr
  have h1 : ∑ l, reweight x y k l = ∑ i, r i * (N * empQ x y i) := by
    have e1 : ∀ l, reweight x y k l = ∑ i, (if x l = i then y l * r i else 0) := by
      intro l
      rw [Finset.sum_ite_eq]; simp only [Finset.mem_univ, if_true, reweight, ratioQ, hr]
    simp_rw [e1]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    have hN' : (N:ℚ) ≠ 0 := by positivity
    have e : r i * (N * empQ x y i) = r i * ∑ l, (if x l = i then y l else 0) := by
      unfold empQ; field_simp
    rw [e, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l _
    split_ifs <;> ring
  rw [h1]
  have h2 : ∀ i, r i * (N * empQ x y i) = k i := by
    intro i
    simp only [hr]
    split_ifs with h
    · rw [h, hsupp i h]; simp
    · have hN' : (N:ℚ) ≠ 0 := by positivity
      field_simp
  simp_rw [h2]
  have := (Finset.Nat.mem_antidiagonalTuple).1 hk
  exact_mod_cast this

lemma sum_le_card {ι : Type*} (s : Finset ι) (X : ι → ℝ) (Y : ℝ) (h : ∀ i ∈ s, X i ≤ Y) :
    ∑ i ∈ s, X i ≤ s.card * Y := by
  have := Finset.sum_le_sum h
  simpa using this

lemma sum_ge_card {ι : Type*} (s : Finset ι) (X : ι → ℝ) (Y : ℝ) (h : ∀ i ∈ s, -Y ≤ X i) :
    -(s.card * Y) ≤ ∑ i ∈ s, X i := by
  have := Finset.sum_le_sum h
  simp at this
  linarith

lemma pos_le_two (a b B : ℝ) (ha : |a| ≤ B) (hb : |b| ≤ B) : pos (a - b) ≤ 2 * B := by
  unfold pos
  apply max_le
  · have := abs_le.1 ha; have := abs_le.1 hb; linarith
  · have := abs_nonneg a; linarith

lemma pos_nonneg (a : ℝ) : 0 ≤ pos a := le_max_right _ _

end WFMFG32


namespace WFMFG48

open Polynomial

variable {d : ℕ}

lemma gf_set (N : ℕ) (p : Fin d → ℝ) (A : Finset (Fin d)) (s : ℝ) :
    ∑ k ∈ Finset.Nat.antidiagonalTuple d N, multW p k * s ^ (∑ i ∈ A, k i)
      = (∑ i, p i + (s - 1) * ∑ i ∈ A, p i) ^ N := by
  classical
  set q : Fin d → ℝ := fun j => if j ∈ A then s * p j else p j with hq
  have hsum : ∑ j, q j = ∑ i, p i + (s - 1) * ∑ i ∈ A, p i := by
    have : ∀ j, q j = p j + (if j ∈ A then (s - 1) * p j else 0) := by
      intro j; simp only [hq]; split_ifs <;> ring
    simp only [this, Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.univ_inter, Finset.mul_sum]
  rw [← hsum, Finset.sum_pow_eq_sum_piAntidiag, ← WFMFGmult.antidiag_eq]
  apply Finset.sum_congr rfl
  intro k _
  have hprod : ∏ j, q j ^ k j = (∏ j, p j ^ k j) * s ^ (∑ i ∈ A, k i) := by
    have : ∀ j, q j ^ k j = p j ^ k j * (if j ∈ A then s ^ (k j) else 1) := by
      intro j; simp only [hq]; split_ifs with h
      · rw [mul_pow, mul_comm]
      · ring
    simp only [this, Finset.prod_mul_distrib, Finset.prod_ite_mem, Finset.univ_inter,
      Finset.prod_pow_eq_pow_sum]
  rw [hprod]; unfold multW; ring

lemma fact_moment (N : ℕ) (p : Fin d → ℝ) (hp : ∑ i, p i = 1) (A : Finset (Fin d)) (r : ℕ) :
    ∑ k ∈ Finset.Nat.antidiagonalTuple d N, multW p k * ((∑ i ∈ A, k i).descFactorial r : ℝ)
      = (N.descFactorial r : ℝ) * (∑ i ∈ A, p i) ^ r := by
  set a := ∑ i ∈ A, p i with ha
  set P : ℝ[X] := ∑ k ∈ Finset.Nat.antidiagonalTuple d N, C (multW p k) * X ^ (∑ i ∈ A, k i)
    with hP
  set q : ℝ[X] := C (1 - a) + C a * X with hq
  have hPQ : P = (X ^ N).comp q := by
    apply Polynomial.funext; intro s
    simp only [hP, hq, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X, eval_comp, eval_add]
    rw [gf_set, hp, ← ha]; ring
  have hit : ∀ (m : ℕ) (f : ℝ[X]),
      derivative^[m] (f.comp q) = C (a ^ m) * (derivative^[m] f).comp q := by
    intro m; induction m with
    | zero => intro f; simp
    | succ m ih =>
      intro f
      rw [Function.iterate_succ_apply', ih, derivative_C_mul, derivative_comp,
        Function.iterate_succ_apply']
      have : derivative q = C a := by simp [hq]
      rw [this, ← mul_assoc, ← C_mul, pow_succ]
  have h1 := congrArg (fun f => (derivative^[r] f).eval 1) hPQ
  simp only [hP, iterate_derivative_sum, iterate_derivative_C_mul, iterate_derivative_X_pow_eq_smul,
    eval_finsetSum, eval_mul, eval_C, eval_smul, eval_pow, eval_X, one_pow, smul_eq_mul,
    mul_one] at h1
  rw [h1, hit, iterate_derivative_X_pow_eq_smul]
  simp [hq]

lemma df_cast (n k : ℕ) : (n.descFactorial (k + 1) : ℝ) = (n.descFactorial k : ℝ) * ((n : ℝ) - k) := by
  rcases le_or_gt k n with h | h
  · rw [Nat.descFactorial_succ, Nat.cast_mul, Nat.cast_sub h]; ring
  · have h0 : n.descFactorial (k + 1) = 0 := Nat.descFactorial_eq_zero_iff_lt.2 (by omega)
    rcases Nat.lt_or_ge n k with h2 | h2
    · have h1 : n.descFactorial k = 0 := Nat.descFactorial_eq_zero_iff_lt.2 h2
      simp [h0, h1]
    · omega

lemma df1 (n : ℕ) : (n.descFactorial 1 : ℝ) = n := by simp
lemma df2 (n : ℕ) : (n.descFactorial 2 : ℝ) = n * (n - 1) := by
  rw [df_cast, df1]; norm_num
lemma df3 (n : ℕ) : (n.descFactorial 3 : ℝ) = n * (n - 1) * (n - 2) := by
  rw [df_cast, df2]; norm_num
lemma df4 (n : ℕ) : (n.descFactorial 4 : ℝ) = n * (n - 1) * (n - 2) * (n - 3) := by
  rw [df_cast, df3]; norm_num

/-- the central fourth moment of `Y_A = ∑_{i ∈ A} k_i` under the multinomial law. -/
lemma central4 (N : ℕ) (p : Fin d → ℝ) (hp : ∑ i, p i = 1) (A : Finset (Fin d)) :
    ∑ k ∈ Finset.Nat.antidiagonalTuple d N,
        multW p k * (((∑ i ∈ A, k i : ℕ) : ℝ) - N * ∑ i ∈ A, p i) ^ 4
      = N * (∑ i ∈ A, p i) * (1 - ∑ i ∈ A, p i)
          * (3 * N * (∑ i ∈ A, p i) * (1 - ∑ i ∈ A, p i)
              - 6 * (∑ i ∈ A, p i) * (1 - ∑ i ∈ A, p i) + 1) := by
  set a := ∑ i ∈ A, p i with ha
  have e : ∀ k : Fin d → ℕ, (((∑ i ∈ A, k i : ℕ) : ℝ) - N * a) ^ 4
      = ((∑ i ∈ A, k i).descFactorial 4 : ℝ) + (6 - 4 * (N * a)) * ((∑ i ∈ A, k i).descFactorial 3 : ℝ)
        + (7 - 12 * (N * a) + 6 * (N * a) ^ 2) * ((∑ i ∈ A, k i).descFactorial 2 : ℝ)
        + (1 - 4 * (N * a) + 6 * (N * a) ^ 2 - 4 * (N * a) ^ 3) * ((∑ i ∈ A, k i).descFactorial 1 : ℝ)
        + (N * a) ^ 4 := by
    intro k; rw [df4, df3, df2, df1]; ring
  have h0 : ∑ k ∈ Finset.Nat.antidiagonalTuple d N, multW p k = 1 := by
    rw [WFMFGmult.multW_sum, hp, one_pow]
  have e2 : ∀ k : Fin d → ℕ, multW p k * (((∑ i ∈ A, k i : ℕ) : ℝ) - N * a) ^ 4
      = multW p k * ((∑ i ∈ A, k i).descFactorial 4 : ℝ)
        + (6 - 4 * (N * a)) * (multW p k * ((∑ i ∈ A, k i).descFactorial 3 : ℝ))
        + (7 - 12 * (N * a) + 6 * (N * a) ^ 2) * (multW p k * ((∑ i ∈ A, k i).descFactorial 2 : ℝ))
        + (1 - 4 * (N * a) + 6 * (N * a) ^ 2 - 4 * (N * a) ^ 3)
            * (multW p k * ((∑ i ∈ A, k i).descFactorial 1 : ℝ))
        + (N * a) ^ 4 * multW p k := by
    intro k; rw [e k]; ring
  rw [Finset.sum_congr rfl (fun k _ => e2 k)]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [fact_moment N p hp A 4, fact_moment N p hp A 3, fact_moment N p hp A 2,
    fact_moment N p hp A 1, h0, df4, df3, df2, df1, ← ha]
  ring

lemma central2 (N : ℕ) (p : Fin d → ℝ) (hp : ∑ i, p i = 1) (A : Finset (Fin d)) :
    ∑ k ∈ Finset.Nat.antidiagonalTuple d N,
        multW p k * (((∑ i ∈ A, k i : ℕ) : ℝ) - N * ∑ i ∈ A, p i) ^ 2
      = N * (∑ i ∈ A, p i) * (1 - ∑ i ∈ A, p i) := by
  set a := ∑ i ∈ A, p i with ha
  have e : ∀ k : Fin d → ℕ, (((∑ i ∈ A, k i : ℕ) : ℝ) - N * a) ^ 2
      = ((∑ i ∈ A, k i).descFactorial 2 : ℝ) + (1 - 2 * (N * a)) * ((∑ i ∈ A, k i).descFactorial 1 : ℝ)
        + (N * a) ^ 2 := by
    intro k; rw [df2, df1]; ring
  have h0 : ∑ k ∈ Finset.Nat.antidiagonalTuple d N, multW p k = 1 := by
    rw [WFMFGmult.multW_sum, hp, one_pow]
  have e2 : ∀ k : Fin d → ℕ, multW p k * (((∑ i ∈ A, k i : ℕ) : ℝ) - N * a) ^ 2
      = multW p k * ((∑ i ∈ A, k i).descFactorial 2 : ℝ)
        + (1 - 2 * (N * a)) * (multW p k * ((∑ i ∈ A, k i).descFactorial 1 : ℝ))
        + (N * a) ^ 2 * multW p k := by
    intro k; rw [e k]; ring
  rw [Finset.sum_congr rfl (fun k _ => e2 k)]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [fact_moment N p hp A 2, fact_moment N p hp A 1, h0, df2, df1, ← ha]
  ring

lemma central1 (N : ℕ) (p : Fin d → ℝ) (hp : ∑ i, p i = 1) (A : Finset (Fin d)) :
    ∑ k ∈ Finset.Nat.antidiagonalTuple d N,
        multW p k * (((∑ i ∈ A, k i : ℕ) : ℝ) - N * ∑ i ∈ A, p i) = 0 := by
  have h0 : ∑ k ∈ Finset.Nat.antidiagonalTuple d N, multW p k = 1 := by
    rw [WFMFGmult.multW_sum, hp, one_pow]
  have := fact_moment N p hp A 1
  simp only [df1, pow_one] at this
  have e2 : ∀ k : Fin d → ℕ, multW p k * (((∑ i ∈ A, k i : ℕ) : ℝ) - N * ∑ i ∈ A, p i)
      = multW p k * ((∑ i ∈ A, k i : ℕ) : ℝ) - (N * ∑ i ∈ A, p i) * multW p k := by
    intro k; ring
  rw [Finset.sum_congr rfl (fun k _ => e2 k), Finset.sum_sub_distrib, ← Finset.mul_sum, this, h0]
  ring

end WFMFG48


namespace WFMFG48I

open WFMFG48 WFMFG32

variable {d : ℕ}

lemma w_sum (N : ℕ) (p : Fin d → ℝ) (hp : ∑ i, p i = 1) :
    ∑ k ∈ Finset.Nat.antidiagonalTuple d N, multW p k = 1 := by
  rw [WFMFGmult.multW_sum, hp, one_pow]

lemma cs (N : ℕ) (p : Fin d → ℝ) (hp0 : ∀ i, 0 ≤ p i) (F G : (Fin d → ℕ) → ℝ) :
    ∑ k ∈ Finset.Nat.antidiagonalTuple d N, multW p k * |F k * G k|
      ≤ Real.sqrt (∑ k ∈ Finset.Nat.antidiagonalTuple d N, multW p k * F k ^ 2)
        * Real.sqrt (∑ k ∈ Finset.Nat.antidiagonalTuple d N, multW p k * G k ^ 2) := by
  set s := Finset.Nat.antidiagonalTuple d N
  have hw : ∀ k, 0 ≤ multW p k := fun k => multW_nonneg p hp0 k
  have h := Finset.sum_mul_sq_le_sq_mul_sq s (fun k => Real.sqrt (multW p k) * |F k|)
    (fun k => Real.sqrt (multW p k) * |G k|)
  have e1 : ∀ k, Real.sqrt (multW p k) * |F k| * (Real.sqrt (multW p k) * |G k|)
      = multW p k * |F k * G k| := by
    intro k
    rw [abs_mul]
    have := Real.mul_self_sqrt (hw k)
    calc _ = (Real.sqrt (multW p k) * Real.sqrt (multW p k)) * (|F k| * |G k|) := by ring
      _ = _ := by rw [this]
  have e2 : ∀ (k) (H : (Fin d → ℕ) → ℝ), (Real.sqrt (multW p k) * |H k|) ^ 2 = multW p k * H k ^ 2 := by
    intro k H
    rw [mul_pow, Real.sq_sqrt (hw k), sq_abs]
  simp only [e1, e2] at h
  have hA : 0 ≤ ∑ k ∈ s, multW p k * |F k * G k| :=
    Finset.sum_nonneg (fun k _ => mul_nonneg (hw k) (abs_nonneg _))
  rw [← Real.sqrt_mul (Finset.sum_nonneg (fun k _ => mul_nonneg (hw k) (sq_nonneg _)))]
  rw [← Real.sqrt_sq hA]
  exact Real.sqrt_le_sqrt h

lemma pm (N : ℕ) (p : Fin d → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp : ∑ i, p i = 1)
    (F : (Fin d → ℕ) → ℝ) (a : ℝ) (ha0 : 0 < a) (ha2 : a ≤ 2) :
    ∑ k ∈ Finset.Nat.antidiagonalTuple d N, multW p k * |F k| ^ a
      ≤ (∑ k ∈ Finset.Nat.antidiagonalTuple d N, multW p k * F k ^ 2) ^ (a / 2) := by
  set s := Finset.Nat.antidiagonalTuple d N
  have hw : ∀ k, 0 ≤ multW p k := fun k => multW_nonneg p hp0 k
  have h := Real.rpow_arith_mean_le_arith_mean_rpow s (fun k => multW p k) (fun k => |F k| ^ a)
    (fun k _ => hw k) (w_sum N p hp) (fun k _ => by positivity) (p := 2 / a)
    (by rw [le_div_iff₀ ha0]; linarith)
  have e : ∀ k, (|F k| ^ a) ^ (2 / a) = F k ^ 2 := by
    intro k
    rw [← Real.rpow_mul (abs_nonneg _), mul_div_cancel₀ _ ha0.ne']
    rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast, sq_abs]
  simp only [e] at h
  have hA : 0 ≤ ∑ k ∈ s, multW p k * |F k| ^ a :=
    Finset.sum_nonneg (fun k _ => mul_nonneg (hw k) (by positivity))
  calc ∑ k ∈ s, multW p k * |F k| ^ a
      = ((∑ k ∈ s, multW p k * |F k| ^ a) ^ (2 / a)) ^ (a / 2) := by
        rw [← Real.rpow_mul hA]
        rw [show 2 / a * (a / 2) = 1 by field_simp, Real.rpow_one]
    _ ≤ _ := Real.rpow_le_rpow (by positivity) h (by positivity)

/-- the coordinate fluctuation `k_j / N - p_j`. -/
noncomputable def Xc (N : ℕ) (p : Fin d → ℝ) (k : Fin d → ℕ) (j : Fin d) : ℝ :=
  (k j : ℝ) / N - p j

lemma Xc_eq (N : ℕ) (hN : 1 ≤ N) (p : Fin d → ℝ) (k : Fin d → ℕ) (j : Fin d) :
    Xc N p k j = ((k j : ℝ) - N * p j) / N := by
  have : (N : ℝ) ≠ 0 := by have : (1:ℝ) ≤ N := by exact_mod_cast hN
                           linarith
  unfold Xc; field_simp

lemma mom1 (N : ℕ) (hN : 1 ≤ N) (p : Fin d → ℝ) (hp : ∑ i, p i = 1) (j : Fin d) :
    ∑ k ∈ Finset.Nat.antidiagonalTuple d N, multW p k * Xc N p k j = 0 := by
  have := central1 N p hp {j}
  simp only [Finset.sum_singleton] at this
  simp only [Xc_eq N hN, mul_div_assoc', ← Finset.sum_div, this, zero_div]

lemma mom2sq (N : ℕ) (hN : 1 ≤ N) (p : Fin d → ℝ) (hp : ∑ i, p i = 1) (j : Fin d) :
    ∑ k ∈ Finset.Nat.antidiagonalTuple d N, multW p k * Xc N p k j ^ 2 = p j * (1 - p j) / N := by
  have := central2 N p hp {j}
  simp only [Finset.sum_singleton] at this
  have hN0 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  simp only [Xc_eq N hN, div_pow, mul_div_assoc', ← Finset.sum_div, this]
  field_simp

lemma mom2 (N : ℕ) (hN : 1 ≤ N) (p : Fin d → ℝ) (hp : ∑ i, p i = 1) (j m : Fin d) :
    ∑ k ∈ Finset.Nat.antidiagonalTuple d N, multW p k * (Xc N p k j * Xc N p k m)
      = (p j * (if j = m then 1 else 0) - p j * p m) / N := by
  by_cases hjm : j = m
  · subst hjm
    simp only [if_true, mul_one, ← sq]
    rw [mom2sq N hN p hp j]; ring
  · simp only [hjm, if_false, mul_zero, zero_sub]
    have hA := central2 N p hp {j, m}
    have hj := central2 N p hp {j}
    have hm := central2 N p hp {m}
    simp only [Finset.sum_singleton, Finset.sum_pair hjm, Nat.cast_add] at hA hj hm
    have hN0 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    have e : ∀ k : Fin d → ℕ, multW p k * (Xc N p k j * Xc N p k m)
        = (multW p k * ((k j : ℝ) + k m - N * (p j + p m)) ^ 2
          - multW p k * ((k j : ℝ) - N * p j) ^ 2 - multW p k * ((k m : ℝ) - N * p m) ^ 2)
          / (2 * N ^ 2) := by
      intro k; rw [Xc_eq N hN, Xc_eq N hN]; field_simp; ring
    rw [Finset.sum_congr rfl (fun k _ => e k), ← Finset.sum_div, Finset.sum_sub_distrib,
      Finset.sum_sub_distrib, hA, hj, hm]
    field_simp; ring

lemma mom4 (N : ℕ) (hN : 1 ≤ N) (p : Fin d → ℝ) (hp : ∑ i, p i = 1) (j : Fin d)
    (hpj0 : 0 ≤ p j) (hpj1 : p j ≤ 1) (hNp : 1 ≤ N * p j) :
    ∑ k ∈ Finset.Nat.antidiagonalTuple d N, multW p k * Xc N p k j ^ 4 ≤ 4 * p j ^ 2 / N ^ 2 := by
  have := central4 N p hp {j}
  simp only [Finset.sum_singleton] at this
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0:ℝ) < N := by linarith
  simp only [Xc_eq N hN, div_pow, mul_div_assoc', ← Finset.sum_div, this]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  set a := p j
  have h1 : N * a * (1 - a) * (3 * N * a * (1 - a) - 6 * a * (1 - a) + 1) ≤ 4 * (N * a) ^ 2 := by
    have ha1 : 0 ≤ 1 - a := by linarith
    have hm : 0 ≤ N * a := by positivity
    have hq : a * (1 - a) ≤ a := by nlinarith
    have hq0 : 0 ≤ a * (1 - a) := mul_nonneg hpj0 ha1
    have t1 : N * a * (1 - a) * (3 * N * a * (1 - a)) ≤ 3 * (N * a) ^ 2 := by
      have : (1 - a) * (a * (1 - a)) ≤ a := by nlinarith
      nlinarith [mul_nonneg hm (mul_nonneg hN0.le hq0)]
    have t2 : N * a * (1 - a) * (1 - 6 * a * (1 - a)) ≤ N * a := by
      have : (1 - a) * (1 - 6 * a * (1 - a)) ≤ 1 := by nlinarith
      nlinarith
    nlinarith
  nlinarith [h1]

end WFMFG48I


namespace WFMFG45

open WFMFG48 WFMFG48I WFMFG32

variable {d : ℕ}

lemma expmom (N : ℕ) (μ : Fin d → ℝ) (hμs : ∑ j, μ j = 1) (i : Fin d) (t : ℝ) :
    ∑ k ∈ Finset.Nat.antidiagonalTuple d N, multW μ k * Real.exp (t * (k i : ℝ))
      = (1 + (Real.exp t - 1) * μ i) ^ N := by
  have := gf_set N μ {i} (Real.exp t)
  simp only [Finset.sum_singleton, hμs] at this
  rw [← this]
  apply Finset.sum_congr rfl; intro k _
  rw [mul_comm t, Real.exp_nat_mul]

/-- `E[exp(t (S_i - m))] ≤ exp(m (e^t - 1 - t))`. -/
lemma expcentral (N : ℕ) (μ : Fin d → ℝ) (hμ0 : ∀ j, 0 ≤ μ j) (hμs : ∑ j, μ j = 1) (i : Fin d)
    (t : ℝ) :
    ∑ k ∈ Finset.Nat.antidiagonalTuple d N,
        multW μ k * Real.exp (t * ((k i : ℝ) - N * μ i))
      ≤ Real.exp (N * μ i * (Real.exp t - 1 - t)) := by
  have hμ1 : μ i ≤ 1 := by
    rw [← hμs]; exact Finset.single_le_sum (f := μ) (fun e _ => hμ0 e) (Finset.mem_univ i)
  have e : ∀ k : Fin d → ℕ, multW μ k * Real.exp (t * ((k i : ℝ) - N * μ i))
      = Real.exp (-(t * (N * μ i))) * (multW μ k * Real.exp (t * (k i : ℝ))) := by
    intro k
    rw [show t * ((k i : ℝ) - N * μ i) = t * (k i : ℝ) + (-(t * (N * μ i))) by ring, Real.exp_add]
    ring
  rw [Finset.sum_congr rfl (fun k _ => e k), ← Finset.mul_sum, expmom N μ hμs i t]
  have hb : 0 ≤ 1 + (Real.exp t - 1) * μ i := by
    have := Real.exp_pos t
    nlinarith [hμ0 i]
  have h1 : (1 + (Real.exp t - 1) * μ i) ^ N ≤ Real.exp ((Real.exp t - 1) * μ i) ^ N :=
    pow_le_pow_left₀ hb (by linarith [Real.add_one_le_exp ((Real.exp t - 1) * μ i)]) N
  rw [← Real.exp_nat_mul] at h1
  calc Real.exp (-(t * (N * μ i))) * (1 + (Real.exp t - 1) * μ i) ^ N
      ≤ Real.exp (-(t * (N * μ i))) * Real.exp (N * ((Real.exp t - 1) * μ i)) :=
        mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
    _ = Real.exp (N * μ i * (Real.exp t - 1 - t)) := by rw [← Real.exp_add]; congr 1; ring

lemma exp_quad (t : ℝ) (ht : |t| ≤ 1) : Real.exp t - 1 - t ≤ t ^ 2 :=
  le_trans (le_abs_self _) (Real.abs_exp_sub_one_sub_id_le ht)

lemma rpow_le_exp (x p : ℝ) (hx : 0 ≤ x) (hp : 0 < p) : x ^ p ≤ p ^ p * Real.exp x := by
  have h1 : x / p ≤ Real.exp (x / p) := by
    have := Real.add_one_le_exp (x / p); linarith
  have h2 : (x / p) ^ p ≤ Real.exp (x / p) ^ p :=
    Real.rpow_le_rpow (by positivity) h1 hp.le
  rw [← Real.exp_mul, div_mul_cancel₀ _ hp.ne', Real.div_rpow hx hp.le] at h2
  rw [div_le_iff₀ (by positivity)] at h2
  linarith

/-- the constant of the Rosenthal-type bound. -/
noncomputable def RC (p : ℝ) : ℝ :=
  2 * Real.exp 1 * p ^ p + 2 ^ p * (2 * p ^ p * (Real.exp 1 * Real.exp (Real.exp 1)) + 1)

lemma RC_nonneg (p : ℝ) (hp : 0 ≤ p) : 0 ≤ RC p := by unfold RC; positivity

/-- A Rosenthal-type moment bound for the binomial marginal: `E|S_i - m|^p ≤ C (m + m^{p/2})`. -/
lemma ros (p : ℝ) (hp : 2 ≤ p) (N : ℕ) (μ : Fin d → ℝ) (hμ0 : ∀ j, 0 ≤ μ j)
    (hμs : ∑ j, μ j = 1) (i : Fin d) :
      ∑ k ∈ Finset.Nat.antidiagonalTuple d N, multW μ k * |(k i : ℝ) - N * μ i| ^ p
        ≤ RC p * (N * μ i + (N * μ i) ^ (p / 2)) := by
  have hp0 : 0 < p := by linarith
  set C1 : ℝ := 2 * Real.exp 1 * p ^ p with hC1
  set C2 : ℝ := 2 ^ p * (2 * p ^ p * (Real.exp 1 * Real.exp (Real.exp 1)) + 1) with hC2
  have hRC : RC p = C1 + C2 := rfl
  rw [hRC]
  set m : ℝ := N * μ i with hm
  have hm0 : 0 ≤ m := mul_nonneg (Nat.cast_nonneg _) (hμ0 i)
  have hw0 : ∀ k, 0 ≤ multW μ k := fun k => multW_nonneg μ hμ0 k
  have hw1 := w_sum N μ hμs
  rcases le_or_gt 1 m with hm1 | hm1
  · -- large mean: exponential moments of the normalized fluctuation
    have hsm : 0 < Real.sqrt m := Real.sqrt_pos.2 (by linarith)
    have hsm2 : Real.sqrt m ^ 2 = m := Real.sq_sqrt hm0
    have hτ : |1 / Real.sqrt m| ≤ 1 := by
      rw [abs_of_pos (by positivity), div_le_one hsm, Real.one_le_sqrt]; exact hm1
    have hτ' : |-(1 / Real.sqrt m)| ≤ 1 := by rwa [abs_neg]
    have hexp : ∀ s : ℝ, |s| ≤ 1 → s ^ 2 = 1 / m →
        ∑ k ∈ Finset.Nat.antidiagonalTuple d N, multW μ k * Real.exp (s * ((k i : ℝ) - m))
          ≤ Real.exp 1 := by
      intro s hs hs2
      refine le_trans (expcentral N μ hμ0 hμs i s) ?_
      apply Real.exp_le_exp.2
      have := exp_quad s hs
      calc m * (Real.exp s - 1 - s) ≤ m * s ^ 2 := mul_le_mul_of_nonneg_left this hm0
        _ = 1 := by rw [hs2]; field_simp
    have hsq : (1 / Real.sqrt m) ^ 2 = 1 / m := by rw [div_pow, hsm2, one_pow]
    have hsq' : (-(1 / Real.sqrt m)) ^ 2 = 1 / m := by rw [neg_sq, hsq]
    have h1 := hexp _ hτ hsq
    have h2 := hexp _ hτ' hsq'
    have hpt : ∀ k : Fin d → ℕ, |(k i : ℝ) - m| ^ p
        ≤ m ^ (p / 2) * (p ^ p * (Real.exp ((1 / Real.sqrt m) * ((k i : ℝ) - m))
          + Real.exp ((-(1 / Real.sqrt m)) * ((k i : ℝ) - m)))) := by
      intro k
      set z := ((k i : ℝ) - m) / Real.sqrt m with hz
      have hzabs : |(k i : ℝ) - m| = Real.sqrt m * |z| := by
        rw [hz, abs_div, abs_of_pos hsm]; field_simp
      have hmp : Real.sqrt m ^ p = m ^ (p / 2) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hm0]; ring_nf
      rw [hzabs, Real.mul_rpow hsm.le (abs_nonneg _), hmp]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      refine le_trans (rpow_le_exp |z| p (abs_nonneg _) hp0) ?_
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have e1 : (1 / Real.sqrt m) * ((k i : ℝ) - m) = z := by rw [hz]; ring
      have e2 : (-(1 / Real.sqrt m)) * ((k i : ℝ) - m) = -z := by rw [hz]; ring
      rw [e1, e2]
      rcases le_total 0 z with hz0 | hz0
      · rw [abs_of_nonneg hz0]; linarith [Real.exp_pos (-z)]
      · rw [abs_of_nonpos hz0]; linarith [Real.exp_pos z]
    calc ∑ k ∈ Finset.Nat.antidiagonalTuple d N, multW μ k * |(k i : ℝ) - N * μ i| ^ p
        ≤ ∑ k ∈ Finset.Nat.antidiagonalTuple d N, multW μ k * (m ^ (p / 2) * (p ^ p *
            (Real.exp ((1 / Real.sqrt m) * ((k i : ℝ) - m))
              + Real.exp ((-(1 / Real.sqrt m)) * ((k i : ℝ) - m))))) :=
          Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_left (hpt k) (hw0 k))
      _ = m ^ (p / 2) * p ^ p *
            (∑ k ∈ Finset.Nat.antidiagonalTuple d N, multW μ k * Real.exp ((1 / Real.sqrt m) * ((k i : ℝ) - m))
            + ∑ k ∈ Finset.Nat.antidiagonalTuple d N, multW μ k *
                Real.exp ((-(1 / Real.sqrt m)) * ((k i : ℝ) - m))) := by
          rw [← Finset.sum_add_distrib, Finset.mul_sum]
          apply Finset.sum_congr rfl; intro k _; ring
      _ ≤ m ^ (p / 2) * p ^ p * (Real.exp 1 + Real.exp 1) :=
          mul_le_mul_of_nonneg_left (add_le_add h1 h2) (by positivity)
      _ = C1 * m ^ (p / 2) := by rw [hC1]; ring
      _ ≤ (C1 + C2) * (m + m ^ (p / 2)) := by
          have : 0 ≤ C2 := by positivity
          have : 0 ≤ C1 := by positivity
          have : 0 ≤ m ^ (p / 2) := by positivity
          nlinarith
  · -- small mean
    have hpt : ∀ k : Fin d → ℕ, |(k i : ℝ) - m| ^ p
        ≤ 2 ^ p * (2 * p ^ p * (Real.exp (k i : ℝ) - 1) + m) := by
      intro k
      have hk0 : (0:ℝ) ≤ k i := by positivity
      have hmax : |(k i : ℝ) - m| ≤ 2 * max (k i : ℝ) m := by
        rw [abs_le]; constructor <;> nlinarith [le_max_left (k i : ℝ) m, le_max_right (k i : ℝ) m]
      have h1 : |(k i : ℝ) - m| ^ p ≤ (2 * max (k i : ℝ) m) ^ p :=
        Real.rpow_le_rpow (abs_nonneg _) hmax hp0.le
      rw [Real.mul_rpow (by norm_num) (le_trans hk0 (le_max_left _ _))] at h1
      refine le_trans h1 (mul_le_mul_of_nonneg_left ?_ (by positivity))
      have hmp : m ^ p ≤ m := by
        exact Real.rpow_le_self_of_le_one hm0 hm1.le (by linarith)
      have hkp : (k i : ℝ) ^ p ≤ 2 * p ^ p * (Real.exp (k i : ℝ) - 1) := by
        rcases Nat.eq_zero_or_pos (k i) with h0 | h0
        · rw [h0]; simp [Real.zero_rpow hp0.ne']
        · have hk1 : (1:ℝ) ≤ k i := by exact_mod_cast h0
          have he : 2 ≤ Real.exp (k i : ℝ) := by
            have := Real.add_one_le_exp (k i : ℝ); linarith
          have := rpow_le_exp (k i : ℝ) p hk0 hp0
          have : 0 ≤ p ^ p := by positivity
          nlinarith
      rcases le_total (k i : ℝ) m with hkm | hkm
      · rw [max_eq_right hkm]
        have : 0 ≤ 2 * p ^ p * (Real.exp (k i : ℝ) - 1) :=
          mul_nonneg (by positivity) (by linarith [Real.add_one_le_exp (k i : ℝ), hk0])
        linarith
      · rw [max_eq_left hkm]; linarith
    have hE : ∑ k ∈ Finset.Nat.antidiagonalTuple d N, multW μ k * (Real.exp (k i : ℝ) - 1)
        ≤ Real.exp 1 * Real.exp (Real.exp 1) * m := by
      have e : ∀ k : Fin d → ℕ, multW μ k * (Real.exp (k i : ℝ) - 1)
          = multW μ k * Real.exp (1 * (k i : ℝ)) - multW μ k := by intro k; rw [one_mul]; ring
      rw [Finset.sum_congr rfl (fun k _ => e k), Finset.sum_sub_distrib, expmom N μ hμs i 1, hw1]
      have he1 : 1 ≤ Real.exp 1 - 1 + 1 := by linarith [Real.add_one_le_exp (1:ℝ)]
      have hb : 0 ≤ 1 + (Real.exp 1 - 1) * μ i := by nlinarith [hμ0 i]
      have h1 : (1 + (Real.exp 1 - 1) * μ i) ^ N ≤ Real.exp ((Real.exp 1 - 1) * μ i) ^ N :=
        pow_le_pow_left₀ hb (by linarith [Real.add_one_le_exp ((Real.exp 1 - 1) * μ i)]) N
      rw [← Real.exp_nat_mul] at h1
      set x := (N:ℝ) * ((Real.exp 1 - 1) * μ i) with hx
      have hx0 : 0 ≤ x := mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (by linarith) (hμ0 i))
      have hxm : x ≤ Real.exp 1 * m := by
        have : x = (Real.exp 1 - 1) * m := by rw [hx, hm]; ring
        rw [this]; nlinarith [Real.exp_pos 1]
      have hxe : x ≤ Real.exp 1 := le_trans hxm (by nlinarith [Real.exp_pos 1])
      have hexpx : Real.exp x - 1 ≤ x * Real.exp x := by
        have h := Real.one_sub_le_exp_neg x
        have := Real.exp_pos x
        have e2 : Real.exp (-x) * Real.exp x = 1 := by rw [← Real.exp_add]; simp
        nlinarith
      have h3 : x * Real.exp x ≤ Real.exp 1 * m * Real.exp (Real.exp 1) :=
        mul_le_mul hxm (Real.exp_le_exp.2 hxe) (Real.exp_pos _).le (by positivity)
      nlinarith
    calc ∑ k ∈ Finset.Nat.antidiagonalTuple d N, multW μ k * |(k i : ℝ) - N * μ i| ^ p
        ≤ ∑ k ∈ Finset.Nat.antidiagonalTuple d N, multW μ k *
            (2 ^ p * (2 * p ^ p * (Real.exp (k i : ℝ) - 1) + m)) :=
          Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_left (hpt k) (hw0 k))
      _ = 2 ^ p * (2 * p ^ p * ∑ k ∈ Finset.Nat.antidiagonalTuple d N,
            multW μ k * (Real.exp (k i : ℝ) - 1) + m * ∑ k ∈ Finset.Nat.antidiagonalTuple d N, multW μ k) := by
          simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl; intro k _; ring
      _ ≤ 2 ^ p * (2 * p ^ p * (Real.exp 1 * Real.exp (Real.exp 1) * m) + m * 1) := by
          rw [hw1]
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have : 0 ≤ 2 * p ^ p := by positivity
          nlinarith
      _ = C2 * m := by rw [hC2]; ring
      _ ≤ (C1 + C2) * (m + m ^ (p / 2)) := by
          have : 0 ≤ C2 := by positivity
          have : 0 ≤ C1 := by positivity
          have : 0 ≤ m ^ (p / 2) := by positivity
          nlinarith

end WFMFG45


namespace WFMFG45

open WFMFG48 WFMFG48I WFMFG32

variable {d : ℕ}

/-- Chernoff bound: `P(|S_i - m| ≥ η' m) ≤ 2 exp(-m η'^2/4)` for `0 < η' ≤ 1`. -/
lemma dev (N : ℕ) (μ : Fin d → ℝ) (hμ0 : ∀ j, 0 ≤ μ j) (hμs : ∑ j, μ j = 1) (i : Fin d)
    (η' : ℝ) (h0 : 0 < η') (h1 : η' ≤ 1) :
    ∑ k ∈ Finset.Nat.antidiagonalTuple d N,
        multW μ k * (if η' * (N * μ i) ≤ |(k i : ℝ) - N * μ i| then 1 else 0)
      ≤ 2 * Real.exp (-(N * μ i * η' ^ 2 / 4)) := by
  set m : ℝ := N * μ i with hm
  have hm0 : 0 ≤ m := mul_nonneg (Nat.cast_nonneg _) (hμ0 i)
  have hw0 : ∀ k, 0 ≤ multW μ k := fun k => multW_nonneg μ hμ0 k
  set lam : ℝ := η' / 2 with hlam
  have hl0 : 0 ≤ lam := by positivity
  have hl1 : |lam| ≤ 1 := by rw [abs_of_nonneg hl0]; linarith
  have hl1' : |-lam| ≤ 1 := by rwa [abs_neg]
  have hpt : ∀ k : Fin d → ℕ, (if η' * m ≤ |(k i : ℝ) - m| then (1:ℝ) else 0)
      ≤ Real.exp (-(lam * (η' * m))) * Real.exp (lam * ((k i : ℝ) - m))
        + Real.exp (-(lam * (η' * m))) * Real.exp ((-lam) * ((k i : ℝ) - m)) := by
    intro k
    split_ifs with hk
    · rcases le_total 0 ((k i : ℝ) - m) with hs | hs
      · rw [abs_of_nonneg hs] at hk
        have : 1 ≤ Real.exp (-(lam * (η' * m))) * Real.exp (lam * ((k i : ℝ) - m)) := by
          rw [← Real.exp_add]; apply Real.one_le_exp; nlinarith
        linarith [Real.exp_pos (-(lam * (η' * m))), Real.exp_pos ((-lam) * ((k i : ℝ) - m)),
          mul_pos (Real.exp_pos (-(lam * (η' * m)))) (Real.exp_pos ((-lam) * ((k i : ℝ) - m)))]
      · rw [abs_of_nonpos hs] at hk
        have : 1 ≤ Real.exp (-(lam * (η' * m))) * Real.exp ((-lam) * ((k i : ℝ) - m)) := by
          rw [← Real.exp_add]; apply Real.one_le_exp; nlinarith
        linarith [mul_pos (Real.exp_pos (-(lam * (η' * m)))) (Real.exp_pos (lam * ((k i : ℝ) - m)))]
    · positivity
  have hA := expcentral N μ hμ0 hμs i lam
  have hB := expcentral N μ hμ0 hμs i (-lam)
  have hqa := exp_quad lam hl1
  have hqb := exp_quad (-lam) hl1'
  calc ∑ k ∈ Finset.Nat.antidiagonalTuple d N,
        multW μ k * (if η' * m ≤ |(k i : ℝ) - m| then 1 else 0)
      ≤ ∑ k ∈ Finset.Nat.antidiagonalTuple d N, multW μ k *
          (Real.exp (-(lam * (η' * m))) * Real.exp (lam * ((k i : ℝ) - m))
            + Real.exp (-(lam * (η' * m))) * Real.exp ((-lam) * ((k i : ℝ) - m))) :=
        Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_left (hpt k) (hw0 k))
    _ = Real.exp (-(lam * (η' * m))) *
          (∑ k ∈ Finset.Nat.antidiagonalTuple d N, multW μ k * Real.exp (lam * ((k i : ℝ) - m))
          + ∑ k ∈ Finset.Nat.antidiagonalTuple d N, multW μ k * Real.exp ((-lam) * ((k i : ℝ) - m))) := by
        rw [← Finset.sum_add_distrib, Finset.mul_sum]
        apply Finset.sum_congr rfl; intro k _; ring
    _ ≤ Real.exp (-(lam * (η' * m))) * (Real.exp (m * lam ^ 2) + Real.exp (m * lam ^ 2)) := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        apply add_le_add
        · exact le_trans hA (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hqa hm0))
        · refine le_trans hB (Real.exp_le_exp.2 ?_)
          rw [neg_sq] at hqb
          exact mul_le_mul_of_nonneg_left hqb hm0
    _ = 2 * Real.exp (-(m * η' ^ 2 / 4)) := by
        rw [← two_mul, mul_left_comm, ← Real.exp_add]
        congr 2; rw [hlam]; ring

/-- `|x - 1| < η' ≤ 1` implies `|x^ℓ - 1| < η' ℓ 2^ℓ`. -/
lemma pow_close (x η' : ℝ) (ℓ : ℕ) (h1 : η' ≤ 1) (hx : |x - 1| < η') :
    |x ^ ℓ - 1| ≤ η' * (ℓ * 2 ^ ℓ) := by
  have hx0 : 0 ≤ x := by have := abs_lt.1 hx; linarith
  have hx2 : x ≤ 2 := by have := abs_lt.1 hx; linarith
  have e : x ^ ℓ - 1 = (x - 1) * ∑ r ∈ Finset.range ℓ, x ^ r := by
    rw [mul_comm]; exact (geom_sum_mul x ℓ).symm
  rw [e, abs_mul]
  have hs : |∑ r ∈ Finset.range ℓ, x ^ r| ≤ ℓ * 2 ^ ℓ := by
    rw [abs_of_nonneg (Finset.sum_nonneg (fun r _ => pow_nonneg hx0 r))]
    calc ∑ r ∈ Finset.range ℓ, x ^ r ≤ ∑ r ∈ Finset.range ℓ, (2:ℝ) ^ ℓ := by
          apply Finset.sum_le_sum; intro r hr
          have := Finset.mem_range.1 hr
          calc x ^ r ≤ 2 ^ r := pow_le_pow_left₀ hx0 hx2 r
            _ ≤ 2 ^ ℓ := pow_le_pow_right₀ (by norm_num) this.le
      _ = ℓ * 2 ^ ℓ := by simp
  exact mul_le_mul hx.le hs (abs_nonneg _) (by linarith [abs_nonneg (x - 1)])

end WFMFG45


namespace WFMFG45

open WFMFG48 WFMFG48I WFMFG32

variable {d : ℕ}

lemma binom_sub_one (Y : ℝ) (ℓ : ℕ) :
    (1 + Y) ^ ℓ - 1 = ∑ k ∈ Finset.Icc 1 ℓ, (ℓ.choose k : ℝ) * Y ^ k := by
  rw [add_comm, add_pow, Finset.sum_range_succ', Nat.choose_zero_right]
  simp only [pow_zero, one_pow, mul_one, Nat.cast_one, add_sub_cancel_right]
  rw [Finset.range_eq_Ico, Finset.sum_Ico_add' (fun k => Y ^ k * (ℓ.choose k : ℝ)) 0 ℓ 1]
  have : Finset.Ico (0 + 1) (ℓ + 1) = Finset.Icc 1 ℓ := by ext; simp
  rw [this]
  apply Finset.sum_congr rfl; intro k _; ring

lemma split12 (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (g : ℕ → ℝ) :
    ∑ k ∈ Finset.Icc 1 ℓ, (ℓ.choose k : ℝ) * g k
      = ℓ * g 1 + (ℓ.choose 2 : ℝ) * g 2 + ∑ k ∈ Finset.Icc 3 ℓ, (ℓ.choose k : ℝ) * g k := by
  rcases Nat.lt_or_ge ℓ 2 with h | h
  · have : ℓ = 1 := by omega
    subst this; simp
  · have e1 : Finset.Icc 1 ℓ = Finset.Ioc 0 ℓ := by ext k; simp; omega
    have e3 : Finset.Icc 3 ℓ = Finset.Ioc 2 ℓ := by ext k; simp; omega
    rw [e1, e3, ← Finset.sum_Ioc_consecutive _ (by norm_num : 0 ≤ 2) h]
    have : Finset.Ioc 0 2 = {1, 2} := by decide
    rw [this, Finset.sum_pair (by norm_num)]
    simp

/-- the normalized fluctuation `S_i/(N μ_i) - 1`. -/
noncomputable def Yv (N : ℕ) (μ : Fin d → ℝ) (k : Fin d → ℕ) (i : Fin d) : ℝ :=
  (k i : ℝ) / (N * μ i) - 1

lemma Yv_eq (N : ℕ) (hN : 1 ≤ N) (μ : Fin d → ℝ) (i : Fin d) (hμi : 0 < μ i) (k : Fin d → ℕ) :
    Yv N μ k i = Xc N μ k i / μ i := by
  have hN0 : (N:ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  unfold Yv Xc; field_simp

lemma Yv_eq' (N : ℕ) (hN : 1 ≤ N) (μ : Fin d → ℝ) (i : Fin d) (hμi : 0 < μ i) (k : Fin d → ℕ) :
    Yv N μ k i = ((k i : ℝ) - N * μ i) / (N * μ i) := by
  have hN0 : (N:ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have := hμi.ne'
  unfold Yv; field_simp

lemma EY1 (N : ℕ) (hN : 1 ≤ N) (μ : Fin d → ℝ) (hμs : ∑ j, μ j = 1) (i : Fin d) (hμi : 0 < μ i) :
    ∑ k ∈ Finset.Nat.antidiagonalTuple d N, multW μ k * Yv N μ k i = 0 := by
  simp only [Yv_eq N hN μ i hμi, mul_div_assoc', ← Finset.sum_div, mom1 N hN μ hμs i, zero_div]

lemma EYY (N : ℕ) (hN : 1 ≤ N) (μ : Fin d → ℝ) (hμs : ∑ j, μ j = 1) (i j : Fin d)
    (hμi : 0 < μ i) (hμj : 0 < μ j) :
    ∑ k ∈ Finset.Nat.antidiagonalTuple d N, multW μ k * (Yv N μ k j * Yv N μ k i)
      = (μ j * (if j = i then 1 else 0) - μ j * μ i) / (N * μ j * μ i) := by
  have e : ∀ k, multW μ k * (Yv N μ k j * Yv N μ k i)
      = (multW μ k * (Xc N μ k j * Xc N μ k i)) / (μ j * μ i) := by
    intro k; rw [Yv_eq N hN μ i hμi, Yv_eq N hN μ j hμj]; field_simp
  rw [Finset.sum_congr rfl (fun k _ => e k), ← Finset.sum_div, mom2 N hN μ hμs j i]
  have : (N:ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  field_simp

lemma EY2 (N : ℕ) (hN : 1 ≤ N) (μ : Fin d → ℝ) (hμs : ∑ j, μ j = 1) (i : Fin d) (hμi : 0 < μ i) :
    ∑ k ∈ Finset.Nat.antidiagonalTuple d N, multW μ k * Yv N μ k i ^ 2
      = (1 - μ i) / (N * μ i) := by
  have := EYY N hN μ hμs i i hμi hμi
  simp only [if_true, ← sq] at this
  rw [this]
  have : (N:ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have := hμi.ne'
  field_simp

lemma EYabs (N : ℕ) (hN : 1 ≤ N) (μ : Fin d → ℝ) (hμ0 : ∀ j, 0 ≤ μ j) (hμs : ∑ j, μ j = 1)
    (i : Fin d) (hμi : 0 < μ i) (q : ℝ) (hq : 2 ≤ q) :
    ∑ k ∈ Finset.Nat.antidiagonalTuple d N, multW μ k * |Yv N μ k i| ^ q
      ≤ RC q * (N * μ i + (N * μ i) ^ (q / 2)) / (N * μ i) ^ q := by
  have hm : 0 < (N:ℝ) * μ i := mul_pos (by exact_mod_cast hN) hμi
  have e : ∀ k, multW μ k * |Yv N μ k i| ^ q
      = (multW μ k * |(k i : ℝ) - N * μ i| ^ q) / (N * μ i) ^ q := by
    intro k
    rw [Yv_eq' N hN μ i hμi, abs_div, abs_of_pos hm, Real.div_rpow (abs_nonneg _) hm.le]
    ring
  rw [Finset.sum_congr rfl (fun k _ => e k), ← Finset.sum_div]
  exact div_le_div_of_nonneg_right (ros q hq N μ hμ0 hμs i) (by positivity)

end WFMFG45


namespace WFMFG45

open WFMFG48 WFMFG48I WFMFG32

variable {d : ℕ}

lemma natpow_rpow (μ : ℝ) (hμ : 0 < μ) (k : ℕ) (hk : 1 ≤ k) :
    μ ^ (k - 1) = μ ^ ((k : ℝ) - 1) := by
  rw [← Real.rpow_natCast, Nat.cast_sub hk, Nat.cast_one]

/-- `(m + m^{k/2}) / m^k ≤ 2 / (N^{k/2} μ^{k-1})` for `k ≥ 2`, `m = N μ`, `0 < μ ≤ 1`. -/
lemma key_bound (N : ℕ) (hN : 1 ≤ N) (μ : ℝ) (h0 : 0 < μ) (h1 : μ ≤ 1) (k : ℕ) (hk : 2 ≤ k) :
    ((N:ℝ) * μ + ((N:ℝ) * μ) ^ ((k:ℝ) / 2)) / ((N:ℝ) * μ) ^ (k:ℝ)
      ≤ 2 / ((N:ℝ) ^ ((k:ℝ) / 2) * μ ^ (k - 1)) := by
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0:ℝ) < N := by linarith
  have hk2 : (2:ℝ) ≤ k := by exact_mod_cast hk
  rw [natpow_rpow μ h0 k (by omega)]
  have hA : 0 < (N:ℝ) ^ ((k:ℝ) / 2) * μ ^ ((k:ℝ) - 1) := by positivity
  rw [div_le_div_iff₀ (by positivity) hA]
  rw [Real.mul_rpow hN0.le h0.le, Real.mul_rpow hN0.le h0.le]
  have t1 : (N:ℝ) * μ * ((N:ℝ) ^ ((k:ℝ) / 2) * μ ^ ((k:ℝ) - 1))
      ≤ (N:ℝ) ^ (k:ℝ) * μ ^ (k:ℝ) := by
    have e : (N:ℝ) * μ * ((N:ℝ) ^ ((k:ℝ) / 2) * μ ^ ((k:ℝ) - 1))
        = (N:ℝ) ^ (1 + (k:ℝ) / 2) * μ ^ (1 + ((k:ℝ) - 1)) := by
      rw [Real.rpow_add hN0, Real.rpow_add h0, Real.rpow_one, Real.rpow_one]; ring
    rw [e, show (1:ℝ) + ((k:ℝ) - 1) = k by ring]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have t2 : (N:ℝ) ^ ((k:ℝ) / 2) * μ ^ ((k:ℝ) / 2) * ((N:ℝ) ^ ((k:ℝ) / 2) * μ ^ ((k:ℝ) - 1))
      ≤ (N:ℝ) ^ (k:ℝ) * μ ^ (k:ℝ) := by
    have e : (N:ℝ) ^ ((k:ℝ) / 2) * μ ^ ((k:ℝ) / 2) * ((N:ℝ) ^ ((k:ℝ) / 2) * μ ^ ((k:ℝ) - 1))
        = (N:ℝ) ^ ((k:ℝ) / 2 + (k:ℝ) / 2) * μ ^ ((k:ℝ) / 2 + ((k:ℝ) - 1)) := by
      rw [Real.rpow_add hN0, Real.rpow_add h0]; ring
    rw [e, show (k:ℝ) / 2 + (k:ℝ) / 2 = k by ring]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact Real.rpow_le_rpow_of_exponent_ge h0 h1 (by linarith)
  nlinarith

/-- the mixed bound `|E[Y_j Y_i^k]| ≤ √(2 RC(2k)) / (N^{(k+1)/2} μ_min^k)`. -/
lemma mixed_bound (N : ℕ) (hN : 1 ≤ N) (μ : Fin d → ℝ) (hμ0 : ∀ j, 0 < μ j) (hμs : ∑ j, μ j = 1)
    (i j : Fin d) (a : ℝ) (ha0 : 0 < a) (hai : a ≤ μ i) (haj : a ≤ μ j) (ha1 : a ≤ 1)
    (k : ℕ) (hk : 1 ≤ k) :
    |∑ s ∈ Finset.Nat.antidiagonalTuple d N, multW μ s * (Yv N μ s j * Yv N μ s i ^ k)|
      ≤ Real.sqrt (2 * RC (2 * k)) / ((N:ℝ) ^ (((k + 1 : ℕ) : ℝ) / 2) * a ^ (k + 1 - 1)) := by
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0:ℝ) < N := by linarith
  have hw0 : ∀ s, 0 ≤ multW μ s := fun s => multW_nonneg μ (fun e => (hμ0 e).le) s
  have hRC := RC_nonneg (2 * (k:ℝ)) (by positivity)
  set mi := (N:ℝ) * μ i with hmi
  have hmi0 : 0 < mi := mul_pos hN0 (hμ0 i)
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have hcs := cs N μ (fun e => (hμ0 e).le) (fun s => Yv N μ s j) (fun s => Yv N μ s i ^ k)
  simp only [abs_mul] at hcs
  have e0 : ∀ s, |multW μ s * (Yv N μ s j * Yv N μ s i ^ k)| = multW μ s * (|Yv N μ s j| * |Yv N μ s i ^ k|) := by
    intro s; rw [abs_mul, abs_of_nonneg (hw0 s), abs_mul]
  simp only [e0]
  refine le_trans hcs ?_
  -- second moments
  have hj2 : ∑ s ∈ Finset.Nat.antidiagonalTuple d N, multW μ s * Yv N μ s j ^ 2 ≤ 1 / ((N:ℝ) * a) := by
    rw [EY2 N hN μ hμs j (hμ0 j)]
    have hj := hμ0 j
    calc (1 - μ j) / (N * μ j) ≤ 1 / (N * μ j) :=
          div_le_div_of_nonneg_right (by linarith) (by positivity)
      _ ≤ 1 / ((N:ℝ) * a) :=
          one_div_le_one_div_of_le (by positivity) (mul_le_mul_of_nonneg_left haj hN0.le)
  have hi2k : ∑ s ∈ Finset.Nat.antidiagonalTuple d N, multW μ s * (Yv N μ s i ^ k) ^ 2
      ≤ RC (2 * k) * (mi + mi ^ k) / mi ^ (2 * k) := by
    have h := EYabs N hN μ (fun e => (hμ0 e).le) hμs i (hμ0 i) (2 * k) (by
      have : (1:ℝ) ≤ k := by exact_mod_cast hk
      linarith)
    have e1 : ∀ s, multW μ s * (Yv N μ s i ^ k) ^ 2 = multW μ s * |Yv N μ s i| ^ ((2 * k : ℕ) : ℝ) := by
      intro s; rw [Real.rpow_natCast, pow_mul, sq_abs, ← pow_mul, ← pow_mul, mul_comm k 2]
    rw [Finset.sum_congr rfl (fun s _ => e1 s)]
    push_cast at h ⊢
    have e2 : mi ^ ((2 * (k:ℝ)) / 2) = mi ^ k := by
      rw [show (2 * (k:ℝ)) / 2 = (k : ℕ) by ring, Real.rpow_natCast]
    have e3 : mi ^ (2 * (k:ℝ)) = mi ^ (2 * k) := by
      rw [show (2 * (k:ℝ)) = ((2 * k : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
    rw [e2, e3] at h
    exact h
  -- the deterministic inequality
  have hgoal : 1 / ((N:ℝ) * a) * (RC (2 * k) * (mi + mi ^ k) / mi ^ (2 * k))
      ≤ (2 * RC (2 * k)) / ((N:ℝ) ^ ((k + 1 : ℕ) : ℝ) * a ^ (2 * k)) := by
    have hNk : (N:ℝ) ^ ((k + 1 : ℕ) : ℝ) = (N:ℝ) ^ (k + 1) := Real.rpow_natCast _ _
    rw [hNk]
    have hrat : (mi + mi ^ k) / mi ^ (2 * k) ≤ 2 / ((N:ℝ) ^ k * a ^ (2 * k - 1)) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have hmipow : mi ^ (2 * k) = (N:ℝ) ^ (2 * k) * μ i ^ (2 * k) := by rw [hmi, mul_pow]
      rcases le_or_gt 1 mi with h1 | h1
      · have hmk : mi ≤ mi ^ k := by
          calc mi = mi ^ 1 := (pow_one mi).symm
            _ ≤ mi ^ k := pow_le_pow_right₀ h1 hk
        have : (mi + mi ^ k) * ((N:ℝ) ^ k * a ^ (2 * k - 1)) ≤ 2 * mi ^ k * ((N:ℝ) ^ k * a ^ (2 * k - 1)) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        refine le_trans this ?_
        have ha' : a ^ (2 * k - 1) ≤ μ i ^ k := by
          calc a ^ (2 * k - 1) ≤ a ^ k := pow_le_pow_of_le_one ha0.le ha1 (by omega)
            _ ≤ μ i ^ k := pow_le_pow_left₀ ha0.le hai k
        have : mi ^ k * ((N:ℝ) ^ k * a ^ (2 * k - 1)) ≤ mi ^ (2 * k) := by
          have e1 : mi ^ k = (N:ℝ) ^ k * μ i ^ k := by rw [hmi, mul_pow]
          have e2 : mi ^ (2 * k) = ((N:ℝ) ^ k * μ i ^ k) * ((N:ℝ) ^ k * μ i ^ k) := by
            rw [hmipow, show 2 * k = k + k by ring, pow_add, pow_add]; ring
          rw [e1, e2]
          apply mul_le_mul_of_nonneg_left _ (by have := (hμ0 i).le; positivity)
          exact mul_le_mul_of_nonneg_left ha' (by positivity)
        linarith
      · have hmk : mi ^ k ≤ mi := by
          calc mi ^ k ≤ mi ^ 1 := pow_le_pow_of_le_one hmi0.le h1.le hk
            _ = mi := pow_one mi
        have : (mi + mi ^ k) * ((N:ℝ) ^ k * a ^ (2 * k - 1)) ≤ 2 * mi * ((N:ℝ) ^ k * a ^ (2 * k - 1)) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        refine le_trans this ?_
        have ha' : a ^ (2 * k - 1) ≤ μ i ^ (2 * k - 1) := pow_le_pow_left₀ ha0.le hai _
        have hNk' : (N:ℝ) ^ k ≤ (N:ℝ) ^ (2 * k - 1) := pow_le_pow_right₀ hN1 (by omega)
        have : mi * ((N:ℝ) ^ k * a ^ (2 * k - 1)) ≤ mi ^ (2 * k) := by
          have e : mi ^ (2 * k) = mi * mi ^ (2 * k - 1) := by
            rw [← pow_succ']; congr 1; omega
          rw [e]
          apply mul_le_mul_of_nonneg_left _ hmi0.le
          rw [hmi, mul_pow]
          exact mul_le_mul hNk' ha' (by positivity) (by positivity)
        linarith
    have : 1 / ((N:ℝ) * a) * (RC (2 * k) * (mi + mi ^ k) / mi ^ (2 * k))
        = RC (2 * k) / ((N:ℝ) * a) * ((mi + mi ^ k) / mi ^ (2 * k)) := by ring
    rw [this]
    calc RC (2 * k) / ((N:ℝ) * a) * ((mi + mi ^ k) / mi ^ (2 * k))
        ≤ RC (2 * k) / ((N:ℝ) * a) * (2 / ((N:ℝ) ^ k * a ^ (2 * k - 1))) :=
          mul_le_mul_of_nonneg_left hrat (by positivity)
      _ = (2 * RC (2 * k)) / ((N:ℝ) ^ (k + 1) * a ^ (2 * k)) := by
          have e : a ^ (2 * k) = a * a ^ (2 * k - 1) := by rw [← pow_succ']; congr 1; omega
          rw [e, pow_succ]; field_simp
  -- take square roots
  have hnn1 : 0 ≤ ∑ s ∈ Finset.Nat.antidiagonalTuple d N, multW μ s * Yv N μ s j ^ 2 :=
    Finset.sum_nonneg (fun s _ => mul_nonneg (hw0 s) (sq_nonneg _))
  have hnn2 : 0 ≤ ∑ s ∈ Finset.Nat.antidiagonalTuple d N, multW μ s * (Yv N μ s i ^ k) ^ 2 :=
    Finset.sum_nonneg (fun s _ => mul_nonneg (hw0 s) (sq_nonneg _))
  rw [← Real.sqrt_mul hnn1]
  have hprod := le_trans (mul_le_mul hj2 hi2k hnn2 (by positivity)) hgoal
  refine le_trans (Real.sqrt_le_sqrt hprod) (le_of_eq ?_)
  rw [Real.sqrt_div' _ (by positivity)]
  congr 1
  rw [show k + 1 - 1 = k by omega]
  rw [Real.sqrt_mul' _ (by positivity), Real.sqrt_eq_rpow, Real.sqrt_eq_rpow,
    ← Real.rpow_mul hN0.le, ← Real.rpow_natCast a (2 * k), ← Real.rpow_mul ha0.le]
  push_cast
  rw [show (2 * (k:ℝ)) * (1 / 2) = (k : ℕ) by ring, Real.rpow_natCast]
  ring_nf

/-- strict version of `pow_close`. -/
lemma pow_close' (x η' : ℝ) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (h1 : η' ≤ 1) (hx : |x - 1| < η') :
    |x ^ ℓ - 1| < η' * (ℓ * 2 ^ ℓ) := by
  have hx0 : 0 ≤ x := by have := abs_lt.1 hx; linarith
  have hx2 : x ≤ 2 := by have := abs_lt.1 hx; linarith
  have e : x ^ ℓ - 1 = (x - 1) * ∑ r ∈ Finset.range ℓ, x ^ r := by
    rw [mul_comm]; exact (geom_sum_mul x ℓ).symm
  rw [e, abs_mul]
  have hs : |∑ r ∈ Finset.range ℓ, x ^ r| ≤ ℓ * 2 ^ ℓ := by
    rw [abs_of_nonneg (Finset.sum_nonneg (fun r _ => pow_nonneg hx0 r))]
    calc ∑ r ∈ Finset.range ℓ, x ^ r ≤ ∑ r ∈ Finset.range ℓ, (2:ℝ) ^ ℓ := by
          apply Finset.sum_le_sum; intro r hr
          have := Finset.mem_range.1 hr
          calc x ^ r ≤ 2 ^ r := pow_le_pow_left₀ hx0 hx2 r
            _ ≤ 2 ^ ℓ := pow_le_pow_right₀ (by norm_num) this.le
      _ = ℓ * 2 ^ ℓ := by simp
  have hpos : (0:ℝ) < ℓ * 2 ^ ℓ := by
    have : (1:ℝ) ≤ ℓ := by exact_mod_cast hℓ
    positivity
  calc |x - 1| * |∑ r ∈ Finset.range ℓ, x ^ r| ≤ |x - 1| * (ℓ * 2 ^ ℓ) :=
        mul_le_mul_of_nonneg_left hs (abs_nonneg _)
    _ < η' * (ℓ * 2 ^ ℓ) := mul_lt_mul_of_pos_right hx hpos

lemma shift_Icc (f : ℕ → ℝ) (a b : ℕ) :
    ∑ k ∈ Finset.Icc a b, f (k + 1) = ∑ k ∈ Finset.Icc (a + 1) (b + 1), f k := by
  have e1 : Finset.Icc a b = Finset.Ico a (b + 1) := by ext; simp
  have e2 : Finset.Icc (a + 1) (b + 1) = Finset.Ico (a + 1) (b + 1 + 1) := by ext; simp
  rw [e1, e2, Finset.sum_Ico_add' f a (b + 1) 1]

end WFMFG45


namespace WFMFG45

open WFMFG48 WFMFG48I WFMFG32

variable {d : ℕ}

lemma x_eq (N : ℕ) (μ : Fin d → ℝ) (s : Fin d → ℕ) (i : Fin d) :
    (s i : ℝ) / (N * μ i) = 1 + Yv N μ s i := by unfold Yv; ring

lemma EYk_abs (N : ℕ) (hN : 1 ≤ N) (μ : Fin d → ℝ) (hμ0 : ∀ j, 0 < μ j) (hμs : ∑ j, μ j = 1)
    (i : Fin d) (k : ℕ) (hk : 2 ≤ k) :
    |∑ s ∈ Finset.Nat.antidiagonalTuple d N, multW μ s * Yv N μ s i ^ k|
      ≤ RC k * (2 / ((N:ℝ) ^ ((k:ℝ) / 2) * μ i ^ (k - 1))) := by
  have hw0 : ∀ s, 0 ≤ multW μ s := fun s => multW_nonneg μ (fun e => (hμ0 e).le) s
  have hμ1 : μ i ≤ 1 := by
    rw [← hμs]; exact Finset.single_le_sum (f := μ) (fun e _ => (hμ0 e).le) (Finset.mem_univ i)
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have e : ∀ s, |multW μ s * Yv N μ s i ^ k| = multW μ s * |Yv N μ s i| ^ (k:ℝ) := by
    intro s; rw [abs_mul, abs_of_nonneg (hw0 s), abs_pow, Real.rpow_natCast]
  rw [Finset.sum_congr rfl (fun s _ => e s)]
  have hk2 : (2:ℝ) ≤ k := by exact_mod_cast hk
  refine le_trans (EYabs N hN μ (fun e => (hμ0 e).le) hμs i (hμ0 i) k hk2) ?_
  rw [mul_div_assoc]
  exact mul_le_mul_of_nonneg_left (key_bound N hN (μ i) (hμ0 i) hμ1 k hk)
    (RC_nonneg _ (by positivity))

theorem partA1 (ℓ : ℕ) (hℓ : 1 ≤ ℓ) : ∃ C : ℝ, ∀ μ ∈ stdSimplex ℝ (Fin d), (∀ i, 0 < μ i) →
    ∀ (i : Fin d) (N : ℕ), 1 ≤ N →
      |multE N μ (fun k => ((k i : ℝ) / (N * μ i)) ^ ℓ - 1)| ≤
        (ℓ : ℝ) * (ℓ - 1) / (2 * N * μ i)
          + C * ∑ k ∈ Finset.Icc 3 ℓ, 1 / ((N : ℝ) ^ ((k : ℝ) / 2) * μ i ^ (k - 1)) := by
  refine ⟨∑ j ∈ Finset.Icc 3 ℓ, (ℓ.choose j : ℝ) * (2 * RC j), ?_⟩
  intro μ hμ hpos i N hN
  have hμs : ∑ j, μ j = 1 := hμ.2
  have hN0 : (0:ℝ) < N := by exact_mod_cast hN
  have hw0 : ∀ s, 0 ≤ multW μ s := fun s => multW_nonneg μ (fun e => (hpos e).le) s
  set g : ℕ → ℝ := fun k => ∑ s ∈ Finset.Nat.antidiagonalTuple d N, multW μ s * Yv N μ s i ^ k with hg
  have hexp : multE N μ (fun k => ((k i : ℝ) / (N * μ i)) ^ ℓ - 1)
      = ∑ k ∈ Finset.Icc 1 ℓ, (ℓ.choose k : ℝ) * g k := by
    unfold multE
    simp only [x_eq, binom_sub_one, Finset.mul_sum, hg]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro k _; apply Finset.sum_congr rfl; intro s _; ring
  have hg1 : g 1 = 0 := by simp only [hg, pow_one]; exact EY1 N hN μ hμs i (hpos i)
  have hg2 : g 2 = (1 - μ i) / (N * μ i) := EY2 N hN μ hμs i (hpos i)
  rw [hexp, split12 ℓ hℓ g, hg1, hg2, mul_zero, zero_add]
  have hμ1 : μ i ≤ 1 := by
    rw [← hμs]; exact Finset.single_le_sum (f := μ) (fun e _ => (hpos e).le) (Finset.mem_univ i)
  have hmain : (ℓ.choose 2 : ℝ) * ((1 - μ i) / (N * μ i)) ≤ (ℓ : ℝ) * (ℓ - 1) / (2 * N * μ i) := by
    rw [Nat.cast_choose_two]
    have hpi := hpos i
    have hl : (0:ℝ) ≤ (ℓ:ℝ) * (ℓ - 1) := by
      have : (1:ℝ) ≤ ℓ := by exact_mod_cast hℓ
      nlinarith
    rw [show (ℓ:ℝ) * (ℓ - 1) / 2 * ((1 - μ i) / (N * μ i)) = ((ℓ:ℝ) * (ℓ - 1)) * (1 - μ i) / (2 * N * μ i)
      by field_simp]
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith
  have hmain0 : 0 ≤ (ℓ.choose 2 : ℝ) * ((1 - μ i) / (N * μ i)) := by
    have := hpos i; apply mul_nonneg (by positivity); apply div_nonneg (by linarith) (by positivity)
  have hrest : |∑ k ∈ Finset.Icc 3 ℓ, (ℓ.choose k : ℝ) * g k|
      ≤ (∑ j ∈ Finset.Icc 3 ℓ, (ℓ.choose j : ℝ) * (2 * RC j))
          * ∑ k ∈ Finset.Icc 3 ℓ, 1 / ((N : ℝ) ^ ((k : ℝ) / 2) * μ i ^ (k - 1)) := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum; intro k hk
    have hk3 : 3 ≤ k := (Finset.mem_Icc.1 hk).1
    rw [abs_mul, abs_of_nonneg (by positivity)]
    have h1 := EYk_abs N hN μ hpos hμs i k (by omega)
    have hT : 0 ≤ 1 / ((N : ℝ) ^ ((k : ℝ) / 2) * μ i ^ (k - 1)) := by have := hpos i; positivity
    have hcoef : (ℓ.choose k : ℝ) * (2 * RC k) ≤ ∑ j ∈ Finset.Icc 3 ℓ, (ℓ.choose j : ℝ) * (2 * RC j) :=
      Finset.single_le_sum (f := fun j => (ℓ.choose j : ℝ) * (2 * RC j))
        (fun j _ => mul_nonneg (by positivity) (by have := RC_nonneg j (by positivity); positivity)) hk
    calc (ℓ.choose k : ℝ) * |g k| ≤ (ℓ.choose k : ℝ) * (RC k * (2 / ((N:ℝ) ^ ((k:ℝ) / 2) * μ i ^ (k - 1)))) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = ((ℓ.choose k : ℝ) * (2 * RC k)) * (1 / ((N : ℝ) ^ ((k : ℝ) / 2) * μ i ^ (k - 1))) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hcoef hT
  calc |(ℓ.choose 2 : ℝ) * ((1 - μ i) / (N * μ i)) + ∑ k ∈ Finset.Icc 3 ℓ, (ℓ.choose k : ℝ) * g k|
      ≤ |(ℓ.choose 2 : ℝ) * ((1 - μ i) / (N * μ i))| + |∑ k ∈ Finset.Icc 3 ℓ, (ℓ.choose k : ℝ) * g k| :=
        abs_add_le _ _
    _ ≤ _ := by rw [abs_of_nonneg hmain0]; linarith

end WFMFG45


namespace WFMFG45

open WFMFG48 WFMFG48I WFMFG32

variable {d : ℕ}

theorem partA2 [NeZero d] (ℓ : ℕ) (hℓ : 1 ≤ ℓ) : ∃ C : ℝ, ∀ μ ∈ stdSimplex ℝ (Fin d), (∀ i, 0 < μ i) →
    ∀ (i j : Fin d) (N : ℕ), 1 ≤ N →
      |multE N μ (fun k => ((k j : ℝ) / (N * μ j)) * (((k i : ℝ) / (N * μ i)) ^ ℓ - 1))| ≤
        (ℓ : ℝ) * (ℓ + 1) / (2 * N * univ.inf' univ_nonempty μ)
          + C * ∑ k ∈ Finset.Icc 3 (ℓ + 1),
              1 / ((N : ℝ) ^ ((k : ℝ) / 2) * (univ.inf' univ_nonempty μ) ^ (k - 1)) := by
  set Cst : ℝ := ∑ j ∈ Finset.Icc 2 ℓ, (ℓ.choose j : ℝ) * (2 * RC j + Real.sqrt (2 * RC (2 * j)))
    with hCst
  have hCst0 : 0 ≤ Cst := Finset.sum_nonneg (fun j _ => mul_nonneg (by positivity)
    (add_nonneg (by have := RC_nonneg j (by positivity); positivity) (Real.sqrt_nonneg _)))
  refine ⟨3 * Cst, ?_⟩
  intro μ hμ hpos i j N hN
  have hμs : ∑ e, μ e = 1 := hμ.2
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0:ℝ) < N := by linarith
  set a := univ.inf' univ_nonempty μ with ha
  have hale : ∀ e, a ≤ μ e := fun e => Finset.inf'_le _ (Finset.mem_univ e)
  have ha0 : 0 < a := by
    obtain ⟨e, _, he⟩ := Finset.exists_mem_eq_inf' (univ_nonempty (α := Fin d)) μ
    rw [ha, he]; exact hpos e
  have hμ1 : ∀ e, μ e ≤ 1 := fun e => by
    rw [← hμs]; exact Finset.single_le_sum (f := μ) (fun e _ => (hpos e).le) (Finset.mem_univ e)
  have ha1 : a ≤ 1 := le_trans (hale i) (hμ1 i)
  set T : ℕ → ℝ := fun k => 1 / ((N : ℝ) ^ ((k : ℝ) / 2) * a ^ (k - 1)) with hT
  have hT0 : ∀ k, 0 ≤ T k := fun k => by simp only [hT]; positivity
  set gA : ℕ → ℝ := fun k => ∑ s ∈ Finset.Nat.antidiagonalTuple d N, multW μ s * Yv N μ s i ^ k
    with hgA
  set gB : ℕ → ℝ := fun k => ∑ s ∈ Finset.Nat.antidiagonalTuple d N,
    multW μ s * (Yv N μ s j * Yv N μ s i ^ k) with hgB
  have hexp : multE N μ (fun k => ((k j : ℝ) / (N * μ j)) * (((k i : ℝ) / (N * μ i)) ^ ℓ - 1))
      = ∑ k ∈ Finset.Icc 1 ℓ, (ℓ.choose k : ℝ) * (gA k + gB k) := by
    unfold multE
    simp only [x_eq N μ _ j, x_eq N μ _ i, binom_sub_one, Finset.mul_sum, hgA, hgB,
      ← Finset.sum_add_distrib]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro k _; apply Finset.sum_congr rfl; intro s _; ring
  have hA1 : gA 1 = 0 := by simp only [hgA, pow_one]; exact EY1 N hN μ hμs i (hpos i)
  have hA2 : gA 2 = (1 - μ i) / (N * μ i) := EY2 N hN μ hμs i (hpos i)
  have hB1 : gB 1 = (μ j * (if j = i then 1 else 0) - μ j * μ i) / (N * μ j * μ i) := by
    simp only [hgB, pow_one]; exact EYY N hN μ hμs i j (hpos i) (hpos j)
  rw [hexp, split12 ℓ hℓ _, hA1, hA2, hB1, zero_add]
  -- main part
  set M : ℝ := (ℓ : ℝ) * ((μ j * (if j = i then 1 else 0) - μ j * μ i) / (N * μ j * μ i))
    + (ℓ.choose 2 : ℝ) * ((1 - μ i) / (N * μ i)) with hM
  have hl1 : (1:ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hMb : |M| ≤ (ℓ : ℝ) * (ℓ + 1) / (2 * N * a) := by
    have hpi := hpos i
    have hpj := hpos j
    have hc2 : (ℓ.choose 2 : ℝ) = ℓ * (ℓ - 1) / 2 := Nat.cast_choose_two ℝ ℓ
    by_cases hji : j = i
    · subst hji
      have e : M = (ℓ * (ℓ + 1) / 2) * ((1 - μ j) / (N * μ j)) := by
        rw [hM, hc2]; simp only [if_true]; field_simp; ring
      rw [e, abs_of_nonneg (by apply mul_nonneg (by positivity); apply div_nonneg (by linarith [hμ1 j]) (by positivity))]
      calc (ℓ * (ℓ + 1) / 2) * ((1 - μ j) / (N * μ j)) ≤ (ℓ * (ℓ + 1) / 2) * (1 / (N * μ j)) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact div_le_div_of_nonneg_right (by linarith) (by positivity)
        _ ≤ (ℓ * (ℓ + 1) / 2) * (1 / (N * a)) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact one_div_le_one_div_of_le (by positivity) (mul_le_mul_of_nonneg_left (hale j) hN0.le)
        _ = (ℓ : ℝ) * (ℓ + 1) / (2 * N * a) := by field_simp
    · have e : M = -(ℓ / N) + (ℓ * (ℓ - 1) / 2) * ((1 - μ i) / (N * μ i)) := by
        rw [hM, hc2]; simp only [hji, if_false]; field_simp; ring
      rw [e]
      have h1 : |-(ℓ / (N:ℝ))| ≤ ℓ / (N * a) := by
        rw [abs_neg, abs_of_nonneg (by positivity)]
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        nlinarith
      have hc0 : (0:ℝ) ≤ ℓ * (ℓ - 1) / 2 := by nlinarith
      have h2 : |(ℓ * (ℓ - 1) / 2) * ((1 - μ i) / (N * μ i))| ≤ (ℓ * (ℓ - 1) / 2) / (N * a) := by
        rw [abs_of_nonneg (mul_nonneg hc0 (div_nonneg (by linarith [hμ1 i]) (by positivity)))]
        calc (ℓ * (ℓ - 1) / 2) * ((1 - μ i) / (N * μ i)) ≤ (ℓ * (ℓ - 1) / 2) * (1 / (N * μ i)) := by
              apply mul_le_mul_of_nonneg_left _ hc0
              exact div_le_div_of_nonneg_right (by linarith) (by positivity)
          _ ≤ (ℓ * (ℓ - 1) / 2) * (1 / (N * a)) := by
              apply mul_le_mul_of_nonneg_left _ hc0
              exact one_div_le_one_div_of_le (by positivity) (mul_le_mul_of_nonneg_left (hale i) hN0.le)
          _ = (ℓ * (ℓ - 1) / 2) / (N * a) := by ring
      calc |-(ℓ / (N:ℝ)) + (ℓ * (ℓ - 1) / 2) * ((1 - μ i) / (N * μ i))|
          ≤ |-(ℓ / (N:ℝ))| + |(ℓ * (ℓ - 1) / 2) * ((1 - μ i) / (N * μ i))| := abs_add_le _ _
        _ ≤ ℓ / (N * a) + (ℓ * (ℓ - 1) / 2) / (N * a) := add_le_add h1 h2
        _ = (ℓ : ℝ) * (ℓ + 1) / (2 * N * a) := by field_simp; ring
  -- remainder
  have hgB : ∀ k, 1 ≤ k → |gB k| ≤ Real.sqrt (2 * RC (2 * k)) * T (k + 1) := by
    intro k hk
    have := mixed_bound N hN μ hpos hμs i j a ha0 (hale i) (hale j) ha1 k hk
    simp only [hgB, hT]
    refine le_trans this (le_of_eq ?_)
    push_cast; ring
  have hgA : ∀ k, 2 ≤ k → |gA k| ≤ 2 * RC k * T k := by
    intro k hk
    have h1 := EYk_abs N hN μ hpos hμs i k hk
    refine le_trans h1 ?_
    have hRC := RC_nonneg k (by positivity)
    simp only [hT]
    rw [show RC k * (2 / ((N:ℝ) ^ ((k:ℝ) / 2) * μ i ^ (k - 1)))
      = 2 * RC k * (1 / ((N:ℝ) ^ ((k:ℝ) / 2) * μ i ^ (k - 1))) by ring]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply one_div_le_one_div_of_le (by positivity)
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha0.le (hale i) _) (by positivity)
  set SI := ∑ k ∈ Finset.Icc 3 (ℓ + 1), T k with hSI
  have hcoef : ∀ k ∈ Finset.Icc 2 ℓ,
      (ℓ.choose k : ℝ) * (2 * RC k + Real.sqrt (2 * RC (2 * k))) ≤ Cst := fun k hk =>
    Finset.single_le_sum (f := fun j => (ℓ.choose j : ℝ) * (2 * RC j + Real.sqrt (2 * RC (2 * j))))
      (fun j _ => mul_nonneg (by positivity)
        (add_nonneg (by have := RC_nonneg j (by positivity); positivity) (Real.sqrt_nonneg _))) hk
  have hR1 : |(ℓ.choose 2 : ℝ) * gB 2| ≤ Cst * SI := by
    rcases Nat.lt_or_ge ℓ 2 with hl | hl
    · have : ℓ = 1 := by omega
      subst this; simp only [Nat.choose_succ_self, Nat.cast_zero, zero_mul, abs_zero]
      exact mul_nonneg hCst0 (Finset.sum_nonneg (fun k _ => hT0 k))
    · rw [abs_mul, abs_of_nonneg (by positivity)]
      have h2 := hgB 2 (by norm_num)
      have hc := hcoef 2 (Finset.mem_Icc.2 ⟨le_rfl, hl⟩)
      have hT3 : T 3 ≤ SI := Finset.single_le_sum (f := T) (fun k _ => hT0 k)
        (Finset.mem_Icc.2 ⟨le_rfl, by omega⟩)
      calc (ℓ.choose 2 : ℝ) * |gB 2| ≤ (ℓ.choose 2 : ℝ) * (Real.sqrt (2 * RC (2 * 2)) * T 3) :=
            mul_le_mul_of_nonneg_left h2 (by positivity)
        _ ≤ ((ℓ.choose 2 : ℝ) * (2 * RC 2 + Real.sqrt (2 * RC (2 * 2)))) * T 3 := by
            have hR := RC_nonneg 2 (by norm_num)
            have hT' := hT0 3
            have hc0 : (0:ℝ) ≤ (ℓ.choose 2 : ℝ) := by positivity
            have := mul_nonneg hc0 (mul_nonneg hR hT')
            push_cast; nlinarith
        _ ≤ Cst * SI := mul_le_mul (by exact_mod_cast hc) hT3 (hT0 3) hCst0
  have hR2 : |∑ k ∈ Finset.Icc 3 ℓ, (ℓ.choose k : ℝ) * (gA k + gB k)| ≤ 2 * Cst * SI := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    have hpt : ∀ k ∈ Finset.Icc 3 ℓ, |(ℓ.choose k : ℝ) * (gA k + gB k)| ≤ Cst * (T k + T (k + 1)) := by
      intro k hk
      have hk3 := (Finset.mem_Icc.1 hk).1
      have hkl := (Finset.mem_Icc.1 hk).2
      rw [abs_mul, abs_of_nonneg (by positivity)]
      have h1 := hgA k (by omega)
      have h2 := hgB k (by omega)
      have hc := hcoef k (Finset.mem_Icc.2 ⟨by omega, hkl⟩)
      have hRC := RC_nonneg k (by positivity)
      have hs := Real.sqrt_nonneg (2 * RC (2 * k))
      have hTk := hT0 k
      have hTk1 := hT0 (k + 1)
      calc (ℓ.choose k : ℝ) * |gA k + gB k| ≤ (ℓ.choose k : ℝ) * (2 * RC k * T k
            + Real.sqrt (2 * RC (2 * k)) * T (k + 1)) :=
            mul_le_mul_of_nonneg_left (le_trans (abs_add_le _ _) (add_le_add h1 h2)) (by positivity)
        _ ≤ ((ℓ.choose k : ℝ) * (2 * RC k + Real.sqrt (2 * RC (2 * k)))) * (T k + T (k + 1)) := by
            have : (0:ℝ) ≤ (ℓ.choose k : ℝ) := by positivity
            push_cast at *; nlinarith [mul_nonneg this (mul_nonneg hs hTk), mul_nonneg this (mul_nonneg hRC hTk1)]
        _ ≤ Cst * (T k + T (k + 1)) := mul_le_mul_of_nonneg_right (by exact_mod_cast hc) (by positivity)
    refine le_trans (Finset.sum_le_sum hpt) ?_
    rw [← Finset.mul_sum, Finset.sum_add_distrib, shift_Icc T 3 ℓ]
    have hs1 : ∑ k ∈ Finset.Icc 3 ℓ, T k ≤ SI :=
      Finset.sum_le_sum_of_subset_of_nonneg (by intro k; simp; omega) (fun k _ _ => hT0 k)
    have hs2 : ∑ k ∈ Finset.Icc (3 + 1) (ℓ + 1), T k ≤ SI :=
      Finset.sum_le_sum_of_subset_of_nonneg (by intro k; simp; omega) (fun k _ _ => hT0 k)
    nlinarith
  have e : (ℓ : ℝ) * ((μ j * (if j = i then 1 else 0) - μ j * μ i) / (N * μ j * μ i))
        + (ℓ.choose 2 : ℝ) * ((1 - μ i) / (N * μ i) + gB 2)
        + ∑ k ∈ Finset.Icc 3 ℓ, (ℓ.choose k : ℝ) * (gA k + gB k)
      = M + ((ℓ.choose 2 : ℝ) * gB 2 + ∑ k ∈ Finset.Icc 3 ℓ, (ℓ.choose k : ℝ) * (gA k + gB k)) := by
    rw [hM]; ring
  rw [e]
  calc |M + ((ℓ.choose 2 : ℝ) * gB 2 + ∑ k ∈ Finset.Icc 3 ℓ, (ℓ.choose k : ℝ) * (gA k + gB k))|
      ≤ |M| + (|(ℓ.choose 2 : ℝ) * gB 2| + |∑ k ∈ Finset.Icc 3 ℓ, (ℓ.choose k : ℝ) * (gA k + gB k)|) :=
        le_trans (abs_add_le _ _) (add_le_add_right (abs_add_le _ _) _)
    _ ≤ (ℓ : ℝ) * (ℓ + 1) / (2 * N * a) + (Cst * SI + 2 * Cst * SI) := by
        have := add_le_add hR1 hR2
        linarith
    _ = _ := by rw [hSI]; ring

end WFMFG45


namespace WFMFG45

open WFMFG48 WFMFG48I WFMFG32

variable {d : ℕ}

lemma pow_sum_le (s : Finset ℕ) (z : ℕ → ℝ) (hz : ∀ k ∈ s, 0 ≤ z k) (p : ℝ) (hp : 1 ≤ p)
    (hs : s.Nonempty) :
    (∑ k ∈ s, z k) ^ p ≤ (s.card : ℝ) ^ (p - 1) * ∑ k ∈ s, z k ^ p := by
  have hc : (0:ℝ) < s.card := by exact_mod_cast hs.card_pos
  have h := Real.rpow_arith_mean_le_arith_mean_rpow s (fun _ => 1 / (s.card : ℝ)) z
    (fun _ _ => by positivity) (by simp [Finset.sum_const]; field_simp) hz hp
  simp only [← Finset.mul_sum] at h
  have hS : 0 ≤ ∑ k ∈ s, z k := Finset.sum_nonneg hz
  rw [Real.mul_rpow (by positivity) hS, Real.div_rpow zero_le_one hc.le, Real.one_rpow] at h
  have hcp : 0 < (s.card : ℝ) ^ p := by positivity
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hcp] at h
  calc (∑ k ∈ s, z k) ^ p ≤ 1 / (s.card : ℝ) * (∑ k ∈ s, z k ^ p) * (s.card : ℝ) ^ p := h
    _ = (s.card : ℝ) ^ (p - 1) * ∑ k ∈ s, z k ^ p := by
        rw [Real.rpow_sub hc, Real.rpow_one]; field_simp

theorem partB (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (p : ℝ) (hp : 2 ≤ p) : ∃ C : ℝ, ∀ μ ∈ stdSimplex ℝ (Fin d),
    (∀ i, 0 < μ i) → ∀ (i : Fin d) (N : ℕ), 1 ≤ N → 1 ≤ (N : ℝ) * μ i →
      (multE N μ (fun k => |((k i : ℝ) / (N * μ i)) ^ ℓ - 1| ^ p)) ^ (1 / p) ≤
        C * ∑ k ∈ Finset.Icc 1 ℓ, ((N : ℝ) * μ i) ^ (-(k : ℝ) / 2) := by
  have hp0 : 0 < p := by linarith
  set B : ℝ := (ℓ : ℝ) ^ (p - 1) * ∑ k ∈ Finset.Icc 1 ℓ, (ℓ.choose k : ℝ) ^ p * (2 * RC (k * p)) with hB
  have hB0 : 0 ≤ B := by
    apply mul_nonneg (by positivity)
    exact Finset.sum_nonneg (fun k _ => mul_nonneg (by positivity)
      (by have := RC_nonneg (k * p) (by positivity); positivity))
  refine ⟨B ^ (1 / p), ?_⟩
  intro μ hμ hpos i N hN hm1
  have hμs : ∑ e, μ e = 1 := hμ.2
  have hw0 : ∀ s, 0 ≤ multW μ s := fun s => multW_nonneg μ (fun e => (hpos e).le) s
  set m : ℝ := N * μ i with hm
  have hm0 : 0 < m := by linarith
  set S : ℝ := ∑ k ∈ Finset.Icc 1 ℓ, m ^ (-(k : ℝ) / 2) with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg (fun k _ => by positivity)
  have hne : (Finset.Icc 1 ℓ).Nonempty := ⟨1, Finset.mem_Icc.2 ⟨le_rfl, hℓ⟩⟩
  have hcard : ((Finset.Icc 1 ℓ).card : ℝ) = ℓ := by simp
  -- pointwise bound
  have hpt : ∀ s : Fin d → ℕ, |((s i : ℝ) / (N * μ i)) ^ ℓ - 1| ^ p
      ≤ (ℓ : ℝ) ^ (p - 1) * ∑ k ∈ Finset.Icc 1 ℓ, (ℓ.choose k : ℝ) ^ p * |Yv N μ s i| ^ ((k:ℝ) * p) := by
    intro s
    rw [x_eq, binom_sub_one]
    have h1 : |∑ k ∈ Finset.Icc 1 ℓ, (ℓ.choose k : ℝ) * Yv N μ s i ^ k|
        ≤ ∑ k ∈ Finset.Icc 1 ℓ, (ℓ.choose k : ℝ) * |Yv N μ s i| ^ k := by
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) (le_of_eq ?_)
      apply Finset.sum_congr rfl; intro k _
      rw [abs_mul, abs_pow, abs_of_nonneg (by positivity)]
    have h2 := Real.rpow_le_rpow (abs_nonneg _) h1 hp0.le
    refine le_trans h2 ?_
    have h3 := pow_sum_le (Finset.Icc 1 ℓ) (fun k => (ℓ.choose k : ℝ) * |Yv N μ s i| ^ k)
      (fun k _ => by positivity) p (by linarith) hne
    rw [hcard] at h3
    refine le_trans h3 (le_of_eq ?_)
    congr 1; apply Finset.sum_congr rfl; intro k _
    rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast,
      ← Real.rpow_mul (abs_nonneg _)]
  -- expectation of each term
  have hterm : ∀ k ∈ Finset.Icc 1 ℓ,
      ∑ s ∈ Finset.Nat.antidiagonalTuple d N, multW μ s * |Yv N μ s i| ^ ((k:ℝ) * p)
        ≤ 2 * RC (k * p) * S ^ p := by
    intro k hk
    have hk1 : (1:ℝ) ≤ k := by exact_mod_cast (Finset.mem_Icc.1 hk).1
    have hq : 2 ≤ (k:ℝ) * p := by nlinarith
    have h1 := EYabs N hN μ (fun e => (hpos e).le) hμs i (hpos i) ((k:ℝ) * p) hq
    refine le_trans h1 ?_
    have hmq : m ≤ m ^ ((k:ℝ) * p / 2) := by
      calc m = m ^ (1:ℝ) := (Real.rpow_one m).symm
        _ ≤ m ^ ((k:ℝ) * p / 2) := Real.rpow_le_rpow_of_exponent_le hm1 (by linarith)
    have hRC := RC_nonneg ((k:ℝ) * p) (by positivity)
    have h2 : RC ((k:ℝ) * p) * (m + m ^ ((k:ℝ) * p / 2)) / m ^ ((k:ℝ) * p)
        ≤ 2 * RC ((k:ℝ) * p) * m ^ (-((k:ℝ) * p / 2)) := by
      rw [div_le_iff₀ (by positivity)]
      have e : m ^ (-((k:ℝ) * p / 2)) * m ^ ((k:ℝ) * p) = m ^ ((k:ℝ) * p / 2) := by
        rw [← Real.rpow_add hm0]; ring_nf
      calc RC ((k:ℝ) * p) * (m + m ^ ((k:ℝ) * p / 2)) ≤ RC ((k:ℝ) * p) * (2 * m ^ ((k:ℝ) * p / 2)) :=
            mul_le_mul_of_nonneg_left (by linarith) hRC
        _ = 2 * RC ((k:ℝ) * p) * m ^ (-((k:ℝ) * p / 2)) * m ^ ((k:ℝ) * p) := by
            rw [mul_assoc (2 * RC ((k:ℝ) * p)), e]; ring
    refine le_trans h2 ?_
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have e2 : m ^ (-((k:ℝ) * p / 2)) = (m ^ (-(k:ℝ) / 2)) ^ p := by
      rw [← Real.rpow_mul hm0.le]; ring_nf
    rw [e2]
    apply Real.rpow_le_rpow (by positivity) _ hp0.le
    have := Finset.single_le_sum (s := Finset.Icc 1 ℓ) (f := fun j : ℕ => m ^ (-(j:ℝ) / 2))
      (fun j _ => by positivity) hk
    exact this
  have hE : multE N μ (fun k => |((k i : ℝ) / (N * μ i)) ^ ℓ - 1| ^ p) ≤ B * S ^ p := by
    unfold multE
    calc ∑ s ∈ Finset.Nat.antidiagonalTuple d N, multW μ s * |((s i : ℝ) / (N * μ i)) ^ ℓ - 1| ^ p
        ≤ ∑ s ∈ Finset.Nat.antidiagonalTuple d N, multW μ s * ((ℓ : ℝ) ^ (p - 1) *
            ∑ k ∈ Finset.Icc 1 ℓ, (ℓ.choose k : ℝ) ^ p * |Yv N μ s i| ^ ((k:ℝ) * p)) :=
          Finset.sum_le_sum (fun s _ => mul_le_mul_of_nonneg_left (hpt s) (hw0 s))
      _ = (ℓ : ℝ) ^ (p - 1) * ∑ k ∈ Finset.Icc 1 ℓ, (ℓ.choose k : ℝ) ^ p *
            ∑ s ∈ Finset.Nat.antidiagonalTuple d N, multW μ s * |Yv N μ s i| ^ ((k:ℝ) * p) := by
          simp only [Finset.mul_sum]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl; intro k _; apply Finset.sum_congr rfl; intro s _; ring
      _ ≤ (ℓ : ℝ) ^ (p - 1) * ∑ k ∈ Finset.Icc 1 ℓ, (ℓ.choose k : ℝ) ^ p * (2 * RC (k * p) * S ^ p) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply Finset.sum_le_sum; intro k hk
          exact mul_le_mul_of_nonneg_left (hterm k hk) (by positivity)
      _ = B * S ^ p := by
          rw [hB, mul_assoc, Finset.sum_mul]
          congr 1; apply Finset.sum_congr rfl; intro k _; ring
  have hE0 : 0 ≤ multE N μ (fun k => |((k i : ℝ) / (N * μ i)) ^ ℓ - 1| ^ p) := by
    unfold multE; exact Finset.sum_nonneg (fun s _ => mul_nonneg (hw0 s) (by positivity))
  calc (multE N μ (fun k => |((k i : ℝ) / (N * μ i)) ^ ℓ - 1| ^ p)) ^ (1 / p)
      ≤ (B * S ^ p) ^ (1 / p) := Real.rpow_le_rpow hE0 hE (by positivity)
    _ = B ^ (1 / p) * S := by
        rw [Real.mul_rpow hB0 (by positivity), ← Real.rpow_mul hS0, mul_one_div_cancel hp0.ne',
          Real.rpow_one]

theorem partC (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (η : ℝ) (hη : 0 < η) : ∃ C c : ℝ, 0 < c ∧
    ∀ μ ∈ stdSimplex ℝ (Fin d), (∀ i, 0 < μ i) → ∀ (i : Fin d) (N : ℕ), 1 ≤ N →
      multE N μ (fun k => if η ≤ |((k i : ℝ) / (N * μ i)) ^ ℓ - 1| then 1 else 0) ≤
        C * Real.exp (-c * N * μ i ^ 2) := by
  have hl : (0:ℝ) < ℓ * 2 ^ ℓ := by
    have : (1:ℝ) ≤ ℓ := by exact_mod_cast hℓ
    positivity
  set η' : ℝ := min 1 (η / (ℓ * 2 ^ ℓ)) with hη'
  have hη'0 : 0 < η' := lt_min one_pos (div_pos hη hl)
  have hη'1 : η' ≤ 1 := min_le_left _ _
  have hη'η : η' * (ℓ * 2 ^ ℓ) ≤ η := by
    have := min_le_right 1 (η / (ℓ * 2 ^ ℓ))
    rw [← hη'] at this
    calc η' * (ℓ * 2 ^ ℓ) ≤ η / (ℓ * 2 ^ ℓ) * (ℓ * 2 ^ ℓ) := mul_le_mul_of_nonneg_right this hl.le
      _ = η := by field_simp
  refine ⟨2, η' ^ 2 / 4, by positivity, ?_⟩
  intro μ hμ hpos i N hN
  have hμs : ∑ e, μ e = 1 := hμ.2
  have hw0 : ∀ s, 0 ≤ multW μ s := fun s => multW_nonneg μ (fun e => (hpos e).le) s
  have hN0 : (0:ℝ) < N := by exact_mod_cast hN
  have hm0 : 0 < (N:ℝ) * μ i := mul_pos hN0 (hpos i)
  have hμ1 : μ i ≤ 1 := by
    rw [← hμs]; exact Finset.single_le_sum (f := μ) (fun e _ => (hpos e).le) (Finset.mem_univ i)
  have hpt : ∀ s : Fin d → ℕ, (if η ≤ |((s i : ℝ) / (N * μ i)) ^ ℓ - 1| then (1:ℝ) else 0)
      ≤ (if η' * (N * μ i) ≤ |(s i : ℝ) - N * μ i| then 1 else 0) := by
    intro s
    by_cases h : η ≤ |((s i : ℝ) / (N * μ i)) ^ ℓ - 1|
    · rw [if_pos h]
      have : η' * (N * μ i) ≤ |(s i : ℝ) - N * μ i| := by
        by_contra hc
        push_neg at hc
        have hx : |(s i : ℝ) / (N * μ i) - 1| < η' := by
          rw [show (s i : ℝ) / (N * μ i) - 1 = ((s i : ℝ) - N * μ i) / (N * μ i) by
              have := hN0.ne'; have := (hpos i).ne'; field_simp,
            abs_div, abs_of_pos hm0, div_lt_iff₀ hm0]
          linarith
        have := pow_close' _ η' ℓ hℓ hη'1 hx
        linarith
      rw [if_pos this]
    · rw [if_neg h]; split_ifs <;> norm_num
  unfold multE
  calc ∑ s ∈ Finset.Nat.antidiagonalTuple d N,
        multW μ s * (if η ≤ |((s i : ℝ) / (N * μ i)) ^ ℓ - 1| then 1 else 0)
      ≤ ∑ s ∈ Finset.Nat.antidiagonalTuple d N,
          multW μ s * (if η' * (N * μ i) ≤ |(s i : ℝ) - N * μ i| then 1 else 0) :=
        Finset.sum_le_sum (fun s _ => mul_le_mul_of_nonneg_left (hpt s) (hw0 s))
    _ ≤ 2 * Real.exp (-(N * μ i * η' ^ 2 / 4)) := dev N μ (fun e => (hpos e).le) hμs i η' hη'0 hη'1
    _ ≤ 2 * Real.exp (-(η' ^ 2 / 4) * N * μ i ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply Real.exp_le_exp.2
        have : μ i ^ 2 ≤ μ i := by nlinarith [hpos i]
        have : 0 ≤ (N:ℝ) * η' ^ 2 / 4 := by positivity
        nlinarith

end WFMFG45

theorem solution (d : ℕ) [NeZero d] :
    (∀ ℓ : ℕ, 1 ≤ ℓ → ∃ C : ℝ, ∀ μ ∈ stdSimplex ℝ (Fin d), (∀ i, 0 < μ i) →
      ∀ (i j : Fin d) (N : ℕ), 1 ≤ N →
        |multE N μ (fun k => ((k i : ℝ) / (N * μ i)) ^ ℓ - 1)| ≤
            (ℓ : ℝ) * (ℓ - 1) / (2 * N * μ i)
              + C * ∑ k ∈ Finset.Icc 3 ℓ, 1 / ((N : ℝ) ^ ((k : ℝ) / 2) * μ i ^ (k - 1)) ∧
        |multE N μ (fun k => ((k j : ℝ) / (N * μ j)) * (((k i : ℝ) / (N * μ i)) ^ ℓ - 1))| ≤
            (ℓ : ℝ) * (ℓ + 1) / (2 * N * univ.inf' univ_nonempty μ)
              + C * ∑ k ∈ Finset.Icc 3 (ℓ + 1),
                  1 / ((N : ℝ) ^ ((k : ℝ) / 2) * (univ.inf' univ_nonempty μ) ^ (k - 1))) ∧
    (∀ ℓ : ℕ, 1 ≤ ℓ → ∀ p : ℝ, 2 ≤ p → ∃ C : ℝ, ∀ μ ∈ stdSimplex ℝ (Fin d), (∀ i, 0 < μ i) →
      ∀ (i : Fin d) (N : ℕ), 1 ≤ N → 1 ≤ (N : ℝ) * μ i →
        (multE N μ (fun k => |((k i : ℝ) / (N * μ i)) ^ ℓ - 1| ^ p)) ^ (1 / p) ≤
          C * ∑ k ∈ Finset.Icc 1 ℓ, ((N : ℝ) * μ i) ^ (-(k : ℝ) / 2)) ∧
    (∀ ℓ : ℕ, 1 ≤ ℓ → ∀ η : ℝ, 0 < η → ∃ C c : ℝ, 0 < c ∧
      ∀ μ ∈ stdSimplex ℝ (Fin d), (∀ i, 0 < μ i) → ∀ (i : Fin d) (N : ℕ), 1 ≤ N →
        multE N μ (fun k => if η ≤ |((k i : ℝ) / (N * μ i)) ^ ℓ - 1| then 1 else 0) ≤
          C * Real.exp (-c * N * μ i ^ 2)) := by
  refine ⟨?_, fun ℓ hℓ p hp => WFMFG45.partB ℓ hℓ p hp, fun ℓ hℓ η hη => WFMFG45.partC ℓ hℓ η hη⟩
  intro ℓ hℓ
  obtain ⟨C1, h1⟩ := WFMFG45.partA1 (d := d) ℓ hℓ
  obtain ⟨C2, h2⟩ := WFMFG45.partA2 (d := d) ℓ hℓ
  refine ⟨max C1 C2, fun μ hμ hpos i j N hN => ⟨?_, ?_⟩⟩
  · refine le_trans (h1 μ hμ hpos i N hN) ?_
    have : 0 ≤ ∑ k ∈ Finset.Icc 3 ℓ, 1 / ((N : ℝ) ^ ((k : ℝ) / 2) * μ i ^ (k - 1)) :=
      Finset.sum_nonneg (fun k _ => by have := hpos i; positivity)
    have := mul_le_mul_of_nonneg_right (le_max_left C1 C2) this
    linarith
  · refine le_trans (h2 μ hμ hpos i j N hN) ?_
    have ha : 0 < univ.inf' univ_nonempty μ := by
      obtain ⟨e, _, he⟩ := Finset.exists_mem_eq_inf' (univ_nonempty (α := Fin d)) μ
      rw [he]; exact hpos e
    have : 0 ≤ ∑ k ∈ Finset.Icc 3 (ℓ + 1),
        1 / ((N : ℝ) ^ ((k : ℝ) / 2) * (univ.inf' univ_nonempty μ) ^ (k - 1)) :=
      Finset.sum_nonneg (fun k _ => by positivity)
    have := mul_le_mul_of_nonneg_right (le_max_right C1 C2) this
    linarith
