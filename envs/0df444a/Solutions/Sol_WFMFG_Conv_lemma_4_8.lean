-- Prove2me | solution 1 for WFMFG.Conv.lemma_4_8
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T18:21:01.351021+00:00
-- url     : https://prove2.me/submissions/917a9888-4de4-43bf-aff8-1c23b7743a5d

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


namespace WFMFG48T

variable {d : ℕ}

lemma affine_line_mem (p v : Fin d → ℝ) (hp : p ∈ affPlane d) (hv : ∑ j, v j = 0) (r : ℝ) :
    p + r • v ∈ affPlane d := by
  show ∑ j, (p + r • v) j = 1
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib, ← Finset.mul_sum, hv,
    mul_zero, add_zero]
  exact hp

lemma comp_line (h : (Fin d → ℝ) → ℝ) (L : (Fin d → ℝ) →L[ℝ] ℝ) (p v : Fin d → ℝ) (r₀ : ℝ)
    (hp : p ∈ affPlane d) (hv : ∑ j, v j = 0)
    (hL : HasFDerivWithinAt h L (affPlane d) (p + r₀ • v)) :
    HasDerivAt (fun r => h (p + r • v)) (L v) r₀ := by
  have hc : HasDerivAt (fun r : ℝ => p + r • v) v r₀ := by
    simpa using ((hasDerivAt_id r₀).smul_const v).const_add p
  have := hL.comp_hasDerivWithinAt r₀ hc.hasDerivWithinAt
    (fun r _ => affine_line_mem p v hp hv r) (s := Set.univ)
  exact hasDerivWithinAt_univ.1 this

lemma Aeq [NeZero d] (h : (Fin d → ℝ) → ℝ) (L : (Fin d → ℝ) →L[ℝ] ℝ) (q v : Fin d → ℝ)
    (hq : q ∈ affPlane d) (hv : ∑ j, v j = 0) (hL : HasFDerivWithinAt h L (affPlane d) q) :
    ∑ j, v j * sD h q j = L v := by
  have hline : ∀ w : Fin d → ℝ, ∑ j, w j = 0 → lineDeriv ℝ h q w = L w := by
    intro w hw
    have := comp_line h L q w 0 hq hw (by simpa using hL)
    unfold lineDeriv
    simpa using this.deriv
  have hw : ∀ j m : Fin d, ∑ i, (Pi.single j (1:ℝ) - Pi.single m (1:ℝ) : Fin d → ℝ) i = 0 := by
    intro j m; simp [Finset.sum_sub_distrib]
  unfold sD
  simp_rw [hline _ (hw _ _)]
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne d
  have key : ∑ j, ∑ m, v j • ((Pi.single j (1:ℝ) : Fin d → ℝ) - Pi.single m 1) = (d : ℝ) • v := by
    funext i
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Pi.single_apply,
      mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero]
    simp [Finset.sum_ite_eq', Finset.sum_const, hv]
  have : ∑ j, v j * ((d : ℝ)⁻¹ * ∑ m, L ((Pi.single j (1:ℝ) : Fin d → ℝ) - Pi.single m 1))
      = (d : ℝ)⁻¹ * L (∑ j, ∑ m, v j • ((Pi.single j (1:ℝ) : Fin d → ℝ) - Pi.single m 1)) := by
    simp only [map_sum, map_smul, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro j _; apply Finset.sum_congr rfl; intro m _; ring
  rw [this, key, map_smul, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hd0, one_mul]

lemma line_deriv_sD [NeZero d] (h : (Fin d → ℝ) → ℝ) (p v : Fin d → ℝ) (r₀ : ℝ)
    (hp : p ∈ affPlane d) (hv : ∑ j, v j = 0)
    (hd : DifferentiableWithinAt ℝ h (affPlane d) (p + r₀ • v)) :
    HasDerivAt (fun r => h (p + r • v)) (∑ j, v j * sD h (p + r₀ • v) j) r₀ := by
  have hL := hd.hasFDerivWithinAt
  rw [Aeq h _ (p + r₀ • v) v (affine_line_mem p v hp hv r₀) hv hL]
  exact comp_line h _ p v r₀ hp hv hL

lemma taylor2 [NeZero d] (h : (Fin d → ℝ) → ℝ) (μ X : Fin d → ℝ) (hμ : μ ∈ affPlane d)
    (hX : ∑ j, X j = 0)
    (hd1 : ∀ r ∈ Set.Icc (0:ℝ) 1, DifferentiableWithinAt ℝ h (affPlane d) (μ + r • X))
    (hd2 : ∀ r ∈ Set.Icc (0:ℝ) 1, ∀ j,
      DifferentiableWithinAt ℝ (fun q => sD h q j) (affPlane d) (μ + r • X))
    (B : ℝ) (hB : ∀ r ∈ Set.Icc (0:ℝ) 1,
      |∑ j, ∑ m, X j * X m * (sD2 h (μ + r • X) m j - sD2 h μ m j)| ≤ B) :
    |h (μ + X) - h μ - ∑ j, X j * sD h μ j - (1 / 2) * ∑ j, ∑ m, X j * X m * sD2 h μ m j| ≤ B := by
  set φ : ℝ → ℝ := fun r => h (μ + r • X) with hφ
  set φ1 : ℝ → ℝ := fun r => ∑ j, X j * sD h (μ + r • X) j with hφ1
  set φ2 : ℝ → ℝ := fun r => ∑ j, ∑ m, X j * X m * sD2 h (μ + r • X) m j with hφ2
  have hD1 : ∀ r ∈ Set.Icc (0:ℝ) 1, HasDerivAt φ (φ1 r) r := fun r hr =>
    line_deriv_sD h μ X r hμ hX (hd1 r hr)
  have hD2 : ∀ r ∈ Set.Icc (0:ℝ) 1, HasDerivAt φ1 (φ2 r) r := by
    intro r hr
    have hj : ∀ j, HasDerivAt (fun r => sD h (μ + r • X) j)
        (∑ m, X m * sD (fun q => sD h q j) (μ + r • X) m) r := fun j =>
      line_deriv_sD (fun q => sD h q j) μ X r hμ hX (hd2 r hr j)
    have := HasDerivAt.fun_sum (u := Finset.univ) (fun j _ => (hj j).const_mul (X j))
    refine this.congr_deriv ?_
    simp only [hφ2, sD2, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro j _; apply Finset.sum_congr rfl; intro m _; ring
  set ψ1 : ℝ → ℝ := fun r => φ1 r - φ1 0 - r * φ2 0 with hψ1
  set ψ : ℝ → ℝ := fun r => φ r - φ 0 - r * φ1 0 - r ^ 2 / 2 * φ2 0 with hψ
  have hψ1d : ∀ r ∈ Set.Icc (0:ℝ) 1, HasDerivWithinAt ψ1 (φ2 r - φ2 0) (Set.Icc 0 1) r := by
    intro r hr
    have := (((hD2 r hr).sub_const (φ1 0)).sub ((hasDerivAt_id r).mul_const (φ2 0)))
    have h3 : HasDerivAt ψ1 (φ2 r - φ2 0) r := by
      refine (this.congr_deriv (by ring)).congr_of_eventuallyEq ?_
      exact Filter.Eventually.of_forall (fun x => by simp [hψ1])
    exact h3.hasDerivWithinAt
  have hb1 : ∀ r ∈ Set.Ico (0:ℝ) 1, ‖φ2 r - φ2 0‖ ≤ B := by
    intro r hr
    have := hB r (Set.Ico_subset_Icc_self hr)
    rw [Real.norm_eq_abs]
    convert this using 2
    simp only [hφ2, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro j _; apply Finset.sum_congr rfl; intro m _
    simp only [zero_smul, add_zero]; ring
  have hψ1b := norm_image_sub_le_of_norm_deriv_le_segment' hψ1d hb1
  have hψd : ∀ r ∈ Set.Icc (0:ℝ) 1, HasDerivWithinAt ψ (ψ1 r) (Set.Icc 0 1) r := by
    intro r hr
    have h1 := ((hD1 r hr).sub_const (φ 0)).sub ((hasDerivAt_id r).mul_const (φ1 0))
    have h2 := ((hasDerivAt_pow 2 r).div_const 2).mul_const (φ2 0)
    have h3 : HasDerivAt ψ (ψ1 r) r := by
      refine ((h1.sub h2).congr_deriv ?_).congr_of_eventuallyEq ?_
      · simp only [hψ1]; push_cast; ring
      · exact Filter.Eventually.of_forall (fun x => by simp [hψ])
    exact h3.hasDerivWithinAt
  have hb2 : ∀ r ∈ Set.Ico (0:ℝ) 1, ‖ψ1 r‖ ≤ B := by
    intro r hr
    have := hψ1b r (Set.Ico_subset_Icc_self hr)
    have h0 : ψ1 0 = 0 := by simp [hψ1]
    rw [h0, sub_zero] at this
    have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hB 0 ⟨le_rfl, zero_le_one⟩)
    calc ‖ψ1 r‖ ≤ B * (r - 0) := this
      _ ≤ B * 1 := mul_le_mul_of_nonneg_left (by linarith [hr.2]) hB0
      _ = B := mul_one B
  have := norm_image_sub_le_of_norm_deriv_le_segment' hψd hb2 1 ⟨zero_le_one, le_rfl⟩
  have h0 : ψ 0 = 0 := by simp [hψ]
  rw [h0, sub_zero, sub_zero, mul_one, Real.norm_eq_abs] at this
  convert this using 2
  simp only [hψ, hφ, hφ1, hφ2, one_smul, zero_smul, add_zero]
  ring

end WFMFG48T


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


namespace WFMFG48P

variable {d : ℕ}

lemma diff_bound (s t a b K H D : ℝ) (ha : b / 2 ≤ a) (hb : 0 < b) (hBt : |b * t| ≤ K)
    (hAB : |a * s - b * t| ≤ H) (hab : |b ^ 2 - a ^ 2| ≤ D) :
    |s - t| ≤ 2 * H / b + 2 * K * D / b ^ 3 := by
  have ha0 : 0 < a := by linarith
  have hK0 : 0 ≤ K := le_trans (abs_nonneg _) hBt
  have hH0 : 0 ≤ H := le_trans (abs_nonneg _) hAB
  have hD0 : 0 ≤ D := le_trans (abs_nonneg _) hab
  have e : s - t = (a * s - b * t) / a + t * (b - a) / a := by field_simp; ring
  have ht : |t| ≤ K / b := by
    rw [le_div_iff₀ hb, mul_comm]; rw [abs_mul, abs_of_pos hb] at hBt; exact hBt
  have hba : |b - a| ≤ D / b := by
    have : b - a = (b ^ 2 - a ^ 2) / (a + b) := by field_simp; ring
    rw [this, abs_div, abs_of_pos (by linarith : 0 < a + b)]
    calc |b ^ 2 - a ^ 2| / (a + b) ≤ D / (a + b) := div_le_div_of_nonneg_right hab (by linarith)
      _ ≤ D / b := div_le_div_of_nonneg_left hD0 hb (by linarith)
  have hinv : 1 / a ≤ 2 / b := by rw [div_le_div_iff₀ ha0 hb]; linarith
  rw [e]
  refine le_trans (abs_add_le _ _) ?_
  rw [abs_div, abs_div, abs_of_pos ha0, abs_mul]
  have h1 : |a * s - b * t| / a ≤ 2 * H / b := by
    calc |a * s - b * t| / a = |a * s - b * t| * (1 / a) := by ring
      _ ≤ H * (2 / b) := mul_le_mul hAB hinv (by positivity) hH0
      _ = 2 * H / b := by ring
  have h2 : |t| * |b - a| / a ≤ 2 * K * D / b ^ 3 := by
    calc |t| * |b - a| / a = |t| * |b - a| * (1 / a) := by ring
      _ ≤ (K / b) * (D / b) * (2 / b) :=
          mul_le_mul (mul_le_mul ht hba (abs_nonneg _) (by positivity)) hinv (by positivity)
            (by positivity)
      _ = 2 * K * D / b ^ 3 := by field_simp
  linarith

lemma norm_rpow_le_sum [NeZero d] (X : Fin d → ℝ) (a : ℝ) (ha : 0 < a) :
    ‖X‖ ^ a ≤ ∑ e, |X e| ^ a := by
  set M := (∑ e, |X e| ^ a) ^ (1 / a) with hM
  have hS : 0 ≤ ∑ e, |X e| ^ a := Finset.sum_nonneg (fun e _ => by positivity)
  have hM0 : 0 ≤ M := by positivity
  have hle : ‖X‖ ≤ M := by
    refine (pi_norm_le_iff_of_nonneg hM0).2 (fun e => ?_)
    rw [Real.norm_eq_abs]
    have h1 : |X e| ^ a ≤ ∑ e, |X e| ^ a :=
      Finset.single_le_sum (f := fun e => |X e| ^ a) (fun e _ => by positivity) (Finset.mem_univ e)
    have := Real.rpow_le_rpow (by positivity) h1 (by positivity : 0 ≤ 1 / a)
    rwa [← Real.rpow_mul (abs_nonneg _), mul_one_div_cancel ha.ne', Real.rpow_one] at this
  calc ‖X‖ ^ a ≤ M ^ a := Real.rpow_le_rpow (norm_nonneg _) hle ha.le
    _ = ∑ e, |X e| ^ a := by
        rw [hM, ← Real.rpow_mul hS, one_div_mul_cancel ha.ne', Real.rpow_one]

lemma sqrt_half (a b c e : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : a / 2 ≤ c) (he : b / 2 ≤ e) :
    Real.sqrt (a * b) / 2 ≤ Real.sqrt (c * e) := by
  have : Real.sqrt (a * b) / 2 = Real.sqrt (a * b / 4) := by
    rw [Real.sqrt_div' _ (by norm_num : (0:ℝ) ≤ 4)]
    rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [this]
  apply Real.sqrt_le_sqrt
  have : a * b / 4 = (a / 2) * (b / 2) := by ring
  rw [this]
  exact mul_le_mul hc he (by positivity) (le_trans (by positivity) hc)

end WFMFG48P


namespace WFMFG48C

open WFMFG48 WFMFG48I WFMFG48T WFMFG48P WFMFG32

variable {d : ℕ}

/-- second-moment bound. -/
lemma L2 (N : ℕ) (hN : 1 ≤ N) (μ : Fin d → ℝ) (hμ0 : ∀ j, 0 < μ j) (hμs : ∑ j, μ j = 1) (j : Fin d) :
    ∑ k ∈ Finset.Nat.antidiagonalTuple d N, multW μ k * Xc N μ k j ^ 2 ≤ μ j / N := by
  rw [mom2sq N hN μ hμs j]
  have hN0 : (0:ℝ) < N := by exact_mod_cast hN
  apply div_le_div_of_nonneg_right _ hN0.le
  nlinarith [hμ0 j]

lemma mu_le_one (μ : Fin d → ℝ) (hμ0 : ∀ j, 0 < μ j) (hμs : ∑ j, μ j = 1) (j : Fin d) : μ j ≤ 1 := by
  rw [← hμs]
  exact Finset.single_le_sum (f := μ) (fun e _ => (hμ0 e).le) (Finset.mem_univ j)

lemma L4 (N : ℕ) (hN : 1 ≤ N) (μ : Fin d → ℝ) (hμ0 : ∀ j, 0 < μ j) (hμs : ∑ j, μ j = 1)
    (hNμ : ∀ j, 1 ≤ N * μ j) (j : Fin d) :
    ∑ k ∈ Finset.Nat.antidiagonalTuple d N, multW μ k * Xc N μ k j ^ 4 ≤ 4 * μ j ^ 2 / N ^ 2 :=
  mom4 N hN μ hμs j (hμ0 j).le (mu_le_one μ hμ0 hμs j) (hNμ j)

/-- `E[(X_j X_m)^2] ≤ 4 μ_j μ_m / N^2`, in square-root form. -/
lemma L3 (N : ℕ) (hN : 1 ≤ N) (μ : Fin d → ℝ) (hμ0 : ∀ j, 0 < μ j) (hμs : ∑ j, μ j = 1)
    (hNμ : ∀ j, 1 ≤ N * μ j) (j m : Fin d) :
    ∑ k ∈ Finset.Nat.antidiagonalTuple d N, multW μ k * (Xc N μ k j * Xc N μ k m) ^ 2
      ≤ 4 * (μ j * μ m) / N ^ 2 := by
  have hN0 : (0:ℝ) < N := by exact_mod_cast hN
  have h := cs N μ (fun e => (hμ0 e).le) (fun k => Xc N μ k j ^ 2) (fun k => Xc N μ k m ^ 2)
  have e1 : ∀ k, |Xc N μ k j ^ 2 * Xc N μ k m ^ 2| = (Xc N μ k j * Xc N μ k m) ^ 2 := by
    intro k; rw [abs_of_nonneg (by positivity)]; ring
  have e2 : ∀ (k : Fin d → ℕ) (e : Fin d), (Xc N μ k e ^ 2) ^ 2 = Xc N μ k e ^ 4 := by
    intro k e; ring
  simp only [e1, e2] at h
  refine le_trans h ?_
  have h4j := L4 N hN μ hμ0 hμs hNμ j
  have h4m := L4 N hN μ hμ0 hμs hNμ m
  have hs : Real.sqrt (4 * μ j ^ 2 / N ^ 2) * Real.sqrt (4 * μ m ^ 2 / N ^ 2) = 4 * (μ j * μ m) / N ^ 2 := by
    rw [← Real.sqrt_mul (by positivity)]
    rw [show 4 * μ j ^ 2 / N ^ 2 * (4 * μ m ^ 2 / N ^ 2) = (4 * (μ j * μ m) / N ^ 2) ^ 2 by ring]
    exact Real.sqrt_sq (by have := hμ0 j; have := hμ0 m; positivity)
  rw [← hs]
  exact mul_le_mul (Real.sqrt_le_sqrt h4j) (Real.sqrt_le_sqrt h4m) (Real.sqrt_nonneg _)
    (Real.sqrt_nonneg _)

lemma sqrt_L3 (N : ℕ) (hN : 1 ≤ N) (μ : Fin d → ℝ) (hμ0 : ∀ j, 0 < μ j) (hμs : ∑ j, μ j = 1)
    (hNμ : ∀ j, 1 ≤ N * μ j) (j m : Fin d) :
    Real.sqrt (∑ k ∈ Finset.Nat.antidiagonalTuple d N, multW μ k * (Xc N μ k j * Xc N μ k m) ^ 2)
      ≤ 2 * Real.sqrt (μ j * μ m) / N := by
  have hN0 : (0:ℝ) < N := by exact_mod_cast hN
  refine le_trans (Real.sqrt_le_sqrt (L3 N hN μ hμ0 hμs hNμ j m)) (le_of_eq ?_)
  rw [show 4 * (μ j * μ m) / N ^ 2 = (2 / N) ^ 2 * (μ j * μ m) by ring,
    Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  ring

lemma sqrt_L2 (N : ℕ) (hN : 1 ≤ N) (μ : Fin d → ℝ) (hμ0 : ∀ j, 0 < μ j) (hμs : ∑ j, μ j = 1)
    (e : Fin d) :
    Real.sqrt (∑ k ∈ Finset.Nat.antidiagonalTuple d N, multW μ k * Xc N μ k e ^ 2)
      ≤ Real.sqrt (μ e / N) := Real.sqrt_le_sqrt (L2 N hN μ hμ0 hμs e)

/-- (L4) `E|X_e X_j X_m| ≤ √(μ_e/N) · 2√(μ_j μ_m)/N`. -/
lemma Lt (N : ℕ) (hN : 1 ≤ N) (μ : Fin d → ℝ) (hμ0 : ∀ j, 0 < μ j) (hμs : ∑ j, μ j = 1)
    (hNμ : ∀ j, 1 ≤ N * μ j) (e j m : Fin d) :
    ∑ k ∈ Finset.Nat.antidiagonalTuple d N, multW μ k * |Xc N μ k e * (Xc N μ k j * Xc N μ k m)|
      ≤ Real.sqrt (μ e / N) * (2 * Real.sqrt (μ j * μ m) / N) :=
  le_trans (cs N μ (fun e => (hμ0 e).le) _ _)
    (mul_le_mul (sqrt_L2 N hN μ hμ0 hμs e) (sqrt_L3 N hN μ hμ0 hμs hNμ j m) (Real.sqrt_nonneg _)
      (Real.sqrt_nonneg _))

/-- (L5) `E[|X_j X_m| |X_e|^{γ'/2}] ≤ 2√(μ_jμ_m)/N · N^{-γ'/4}`. -/
lemma Lh (N : ℕ) (hN : 1 ≤ N) (μ : Fin d → ℝ) (hμ0 : ∀ j, 0 < μ j) (hμs : ∑ j, μ j = 1)
    (hNμ : ∀ j, 1 ≤ N * μ j) (γ' : ℝ) (hγ0 : 0 < γ') (hγ1 : γ' < 1) (e j m : Fin d) :
    ∑ k ∈ Finset.Nat.antidiagonalTuple d N,
        multW μ k * |(Xc N μ k j * Xc N μ k m) * |Xc N μ k e| ^ (γ' / 2)|
      ≤ (2 * Real.sqrt (μ j * μ m) / N) * (N : ℝ) ^ (-(γ' / 4)) := by
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0:ℝ) < N := by linarith
  refine le_trans (cs N μ (fun e => (hμ0 e).le) _ _) ?_
  refine mul_le_mul (sqrt_L3 N hN μ hμ0 hμs hNμ j m) ?_ (Real.sqrt_nonneg _) (by positivity)
  have e1 : ∀ k, (|Xc N μ k e| ^ (γ' / 2)) ^ 2 = |Xc N μ k e| ^ γ' := by
    intro k
    rw [← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _)]; norm_num
  simp only [e1]
  have hpm := pm N μ (fun e => (hμ0 e).le) hμs (fun k => Xc N μ k e) γ' hγ0 (by linarith)
  have hL2 := L2 N hN μ hμ0 hμs e
  have hle1 : μ e / N ≤ 1 / N :=
    div_le_div_of_nonneg_right (mu_le_one μ hμ0 hμs e) hN0.le
  have h2 : (∑ k ∈ Finset.Nat.antidiagonalTuple d N, multW μ k * Xc N μ k e ^ 2) ^ (γ' / 2)
      ≤ (1 / (N:ℝ)) ^ (γ' / 2) :=
    Real.rpow_le_rpow (Finset.sum_nonneg (fun k _ => mul_nonneg (multW_nonneg _ (fun e => (hμ0 e).le) _)
      (sq_nonneg _))) (le_trans hL2 hle1) (by positivity)
  calc Real.sqrt (∑ k ∈ Finset.Nat.antidiagonalTuple d N, multW μ k * |Xc N μ k e| ^ γ')
      ≤ Real.sqrt ((1 / (N:ℝ)) ^ (γ' / 2)) := Real.sqrt_le_sqrt (le_trans hpm h2)
    _ = (N : ℝ) ^ (-(γ' / 4)) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity), one_div, Real.inv_rpow hN0.le,
          ← Real.rpow_neg hN0.le]
        ring_nf

/-- (L6) `E|X_j X_m^2| ≤ √(μ_j/N) · 2μ_m/N`. -/
lemma Lq (N : ℕ) (hN : 1 ≤ N) (μ : Fin d → ℝ) (hμ0 : ∀ j, 0 < μ j) (hμs : ∑ j, μ j = 1)
    (hNμ : ∀ j, 1 ≤ N * μ j) (j m : Fin d) :
    ∑ k ∈ Finset.Nat.antidiagonalTuple d N, multW μ k * |Xc N μ k j * Xc N μ k m ^ 2|
      ≤ Real.sqrt (μ j / N) * (2 * μ m / N) := by
  have hN0 : (0:ℝ) < N := by exact_mod_cast hN
  refine le_trans (cs N μ (fun e => (hμ0 e).le) _ _) ?_
  refine mul_le_mul (sqrt_L2 N hN μ hμ0 hμs j) ?_ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have e2 : ∀ (k : Fin d → ℕ), (Xc N μ k m ^ 2) ^ 2 = Xc N μ k m ^ 4 := by intro k; ring
  simp only [e2]
  refine le_trans (Real.sqrt_le_sqrt (L4 N hN μ hμ0 hμs hNμ m)) (le_of_eq ?_)
  rw [show 4 * μ m ^ 2 / N ^ 2 = (2 * μ m / N) ^ 2 by ring]
  exact Real.sqrt_sq (by have := hμ0 m; positivity)

end WFMFG48C


namespace WFMFG48C

open WFMFG48 WFMFG48I WFMFG48T WFMFG48P WFMFG32

variable {d : ℕ}

lemma sqrt_ge_nu (ν a c : ℝ) (hν : 0 ≤ ν) (ha : ν ≤ a) (hc : ν ≤ c) : ν ≤ Real.sqrt (a * c) := by
  rw [Real.le_sqrt hν (by nlinarith)]; nlinarith

lemma EB1 [NeZero d] (N : ℕ) (hN : 1 ≤ N) (μ : Fin d → ℝ) (hμ0 : ∀ j, 0 < μ j)
    (hμs : ∑ j, μ j = 1) (hNμ : ∀ j, 1 ≤ N * μ j) (γ' K : ℝ) (hγ0 : 0 < γ') (hγ1 : γ' < 1)
    (hK0 : 0 ≤ K) (j m : Fin d) :
    (N:ℝ) * ∑ k ∈ Finset.Nat.antidiagonalTuple d N, multW μ k *
        (|Xc N μ k j * Xc N μ k m| * (2 * K * (∑ e, |Xc N μ k e| ^ (γ' / 2))
          / Real.sqrt (μ m * μ j)))
      ≤ 4 * K * d * (N:ℝ) ^ (-(γ' / 4)) := by
  have hN0 : (0:ℝ) < N := by exact_mod_cast hN
  set b := Real.sqrt (μ m * μ j) with hb
  have hb0 : 0 < b := Real.sqrt_pos.2 (mul_pos (hμ0 m) (hμ0 j))
  have hbb : Real.sqrt (μ j * μ m) = b := by rw [hb, mul_comm]
  have e : ∀ k, multW μ k * (|Xc N μ k j * Xc N μ k m| * (2 * K * (∑ e, |Xc N μ k e| ^ (γ' / 2)) / b))
      = (2 * K / b) * ∑ e, multW μ k * |(Xc N μ k j * Xc N μ k m) * |Xc N μ k e| ^ (γ' / 2)| := by
    intro k
    have hsum : ∑ e, multW μ k * |(Xc N μ k j * Xc N μ k m) * |Xc N μ k e| ^ (γ' / 2)|
        = multW μ k * |Xc N μ k j * Xc N μ k m| * ∑ e, |Xc N μ k e| ^ (γ' / 2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro e _
      rw [abs_mul (Xc N μ k j * Xc N μ k m), abs_of_nonneg (by positivity : (0:ℝ) ≤ |Xc N μ k e| ^ (γ' / 2))]
      ring
    rw [hsum]
    have hbne : b ≠ 0 := hb0.ne'
    field_simp
  rw [Finset.sum_congr rfl (fun k _ => e k), ← Finset.mul_sum, Finset.sum_comm]
  have hbound : ∀ e : Fin d, ∑ k ∈ Finset.Nat.antidiagonalTuple d N,
      multW μ k * |(Xc N μ k j * Xc N μ k m) * |Xc N μ k e| ^ (γ' / 2)|
        ≤ (2 * b / N) * (N : ℝ) ^ (-(γ' / 4)) := by
    intro e; rw [← hbb]; exact Lh N hN μ hμ0 hμs hNμ γ' hγ0 hγ1 e j m
  have hsum := Finset.sum_le_sum (fun e (_ : e ∈ Finset.univ) => hbound e)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have hpos : 0 ≤ (N:ℝ) * (2 * K / b) := by positivity
  calc (N:ℝ) * ((2 * K / b) * ∑ e, ∑ k ∈ Finset.Nat.antidiagonalTuple d N,
          multW μ k * |(Xc N μ k j * Xc N μ k m) * |Xc N μ k e| ^ (γ' / 2)|)
      = (N * (2 * K / b)) * ∑ e, ∑ k ∈ Finset.Nat.antidiagonalTuple d N,
          multW μ k * |(Xc N μ k j * Xc N μ k m) * |Xc N μ k e| ^ (γ' / 2)| := by ring
    _ ≤ (N * (2 * K / b)) * (d * ((2 * b / N) * (N : ℝ) ^ (-(γ' / 4)))) :=
        mul_le_mul_of_nonneg_left hsum hpos
    _ = 4 * K * d * (N:ℝ) ^ (-(γ' / 4)) := by field_simp; ring

lemma EB2 [NeZero d] (N : ℕ) (hN : 1 ≤ N) (μ : Fin d → ℝ) (hμ0 : ∀ j, 0 < μ j)
    (hμs : ∑ j, μ j = 1) (hNμ : ∀ j, 1 ≤ N * μ j) (K ν : ℝ) (hK0 : 0 ≤ K) (hν0 : 0 < ν)
    (hνμ : ∀ j, ν ≤ μ j) (j m : Fin d) :
    (N:ℝ) * ∑ k ∈ Finset.Nat.antidiagonalTuple d N, multW μ k *
        (|Xc N μ k j * Xc N μ k m| * (2 * K * (|Xc N μ k m| * μ j + |Xc N μ k j| * μ m
          + |Xc N μ k m * Xc N μ k j|) / Real.sqrt (μ m * μ j) ^ 3))
      ≤ 16 * K / (ν * Real.sqrt N) := by
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0:ℝ) < N := by linarith
  set b := Real.sqrt (μ m * μ j) with hb
  have hb0 : 0 < b := Real.sqrt_pos.2 (mul_pos (hμ0 m) (hμ0 j))
  have hb2 : b ^ 2 = μ m * μ j := Real.sq_sqrt (by have := hμ0 m; have := hμ0 j; positivity)
  have hbν : ν ≤ b := sqrt_ge_nu ν _ _ hν0.le (hνμ m) (hνμ j)
  have hw0 : ∀ k, 0 ≤ multW μ k := fun k => multW_nonneg μ (fun e => (hμ0 e).le) k
  have e : ∀ k, multW μ k * (|Xc N μ k j * Xc N μ k m| * (2 * K * (|Xc N μ k m| * μ j
          + |Xc N μ k j| * μ m + |Xc N μ k m * Xc N μ k j|) / b ^ 3))
      = (2 * K / b ^ 3) * (μ j * (multW μ k * |Xc N μ k j * Xc N μ k m ^ 2|)
          + μ m * (multW μ k * |Xc N μ k m * Xc N μ k j ^ 2|)
          + multW μ k * (Xc N μ k j * Xc N μ k m) ^ 2) := by
    intro k
    have a1 : |Xc N μ k j * Xc N μ k m| = |Xc N μ k j| * |Xc N μ k m| := abs_mul _ _
    have a2 : |Xc N μ k m * Xc N μ k j| = |Xc N μ k m| * |Xc N μ k j| := abs_mul _ _
    have a3 : |Xc N μ k j * Xc N μ k m ^ 2| = |Xc N μ k j| * |Xc N μ k m| ^ 2 := by
      rw [abs_mul, abs_pow]
    have a4 : |Xc N μ k m * Xc N μ k j ^ 2| = |Xc N μ k m| * |Xc N μ k j| ^ 2 := by
      rw [abs_mul, abs_pow]
    have a5 : (Xc N μ k j * Xc N μ k m) ^ 2 = |Xc N μ k j| ^ 2 * |Xc N μ k m| ^ 2 := by
      rw [mul_pow, sq_abs, sq_abs]
    have hbne : b ≠ 0 := hb0.ne'
    rw [a1, a2, a3, a4, a5]
    field_simp
  rw [Finset.sum_congr rfl (fun k _ => e k), ← Finset.mul_sum, Finset.sum_add_distrib,
    Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have h1 := Lq N hN μ hμ0 hμs hNμ j m
  have h2 := Lq N hN μ hμ0 hμs hNμ m j
  have h3 := L3 N hN μ hμ0 hμs hNμ j m
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  have hsq : ∀ e, Real.sqrt (μ e / N) ≤ 1 / Real.sqrt N := by
    intro e
    rw [Real.sqrt_div' _ hN0.le]
    apply div_le_div_of_nonneg_right _ hsN.le
    rw [Real.sqrt_le_one]; exact mu_le_one μ hμ0 hμs e
  have hNs : 1 / (N:ℝ) ≤ 1 / Real.sqrt N := by
    apply one_div_le_one_div_of_le hsN
    have : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hN0.le
    have : 1 ≤ Real.sqrt N := by rw [Real.one_le_sqrt]; exact hN1
    nlinarith
  -- bound the bracket
  have hbr : μ j * ∑ k ∈ Finset.Nat.antidiagonalTuple d N, multW μ k * |Xc N μ k j * Xc N μ k m ^ 2|
      + μ m * ∑ k ∈ Finset.Nat.antidiagonalTuple d N, multW μ k * |Xc N μ k m * Xc N μ k j ^ 2|
      + ∑ k ∈ Finset.Nat.antidiagonalTuple d N, multW μ k * (Xc N μ k j * Xc N μ k m) ^ 2
      ≤ (μ m * μ j) * (8 / (N * Real.sqrt N)) := by
    have hμj := (hμ0 j).le
    have hμm := (hμ0 m).le
    have t1 : μ j * ∑ k ∈ Finset.Nat.antidiagonalTuple d N, multW μ k * |Xc N μ k j * Xc N μ k m ^ 2|
        ≤ μ j * ((1 / Real.sqrt N) * (2 * μ m / N)) :=
      mul_le_mul_of_nonneg_left (le_trans h1 (mul_le_mul_of_nonneg_right (hsq j) (by positivity))) hμj
    have t2 : μ m * ∑ k ∈ Finset.Nat.antidiagonalTuple d N, multW μ k * |Xc N μ k m * Xc N μ k j ^ 2|
        ≤ μ m * ((1 / Real.sqrt N) * (2 * μ j / N)) :=
      mul_le_mul_of_nonneg_left (le_trans h2 (mul_le_mul_of_nonneg_right (hsq m) (by positivity))) hμm
    have t3 : 4 * (μ j * μ m) / N ^ 2 ≤ (μ m * μ j) * (4 / (N * Real.sqrt N)) := by
      have : 4 * (μ j * μ m) / N ^ 2 = (μ m * μ j) * (4 / N) * (1 / N) := by field_simp
      rw [this]
      have : (μ m * μ j) * (4 / (N * Real.sqrt N)) = (μ m * μ j) * (4 / N) * (1 / Real.sqrt N) := by
        field_simp
      rw [this]
      exact mul_le_mul_of_nonneg_left hNs (by positivity)
    have e1 : μ j * ((1 / Real.sqrt N) * (2 * μ m / N)) = (μ m * μ j) * (2 / (N * Real.sqrt N)) := by
      field_simp
    have e2 : μ m * ((1 / Real.sqrt N) * (2 * μ j / N)) = (μ m * μ j) * (2 / (N * Real.sqrt N)) := by
      field_simp
    have e3 : (μ m * μ j) * (8 / (N * Real.sqrt N)) = (μ m * μ j) * (2 / (N * Real.sqrt N))
        + (μ m * μ j) * (2 / (N * Real.sqrt N)) + (μ m * μ j) * (4 / (N * Real.sqrt N)) := by ring
    rw [e3]; rw [e1] at t1; rw [e2] at t2
    linarith
  have hpos : 0 ≤ (N:ℝ) * (2 * K / b ^ 3) := by positivity
  calc (N:ℝ) * ((2 * K / b ^ 3) * (μ j * ∑ k ∈ Finset.Nat.antidiagonalTuple d N,
          multW μ k * |Xc N μ k j * Xc N μ k m ^ 2|
        + μ m * ∑ k ∈ Finset.Nat.antidiagonalTuple d N, multW μ k * |Xc N μ k m * Xc N μ k j ^ 2|
        + ∑ k ∈ Finset.Nat.antidiagonalTuple d N, multW μ k * (Xc N μ k j * Xc N μ k m) ^ 2))
      = ((N:ℝ) * (2 * K / b ^ 3)) * (μ j * ∑ k ∈ Finset.Nat.antidiagonalTuple d N,
          multW μ k * |Xc N μ k j * Xc N μ k m ^ 2|
        + μ m * ∑ k ∈ Finset.Nat.antidiagonalTuple d N, multW μ k * |Xc N μ k m * Xc N μ k j ^ 2|
        + ∑ k ∈ Finset.Nat.antidiagonalTuple d N, multW μ k * (Xc N μ k j * Xc N μ k m) ^ 2) := by ring
    _ ≤ ((N:ℝ) * (2 * K / b ^ 3)) * ((μ m * μ j) * (8 / (N * Real.sqrt N))) :=
        mul_le_mul_of_nonneg_left hbr hpos
    _ = 16 * K / (b * Real.sqrt N) := by
        rw [← hb2]; field_simp; ring
    _ ≤ 16 * K / (ν * Real.sqrt N) := by
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        exact mul_le_mul_of_nonneg_right hbν hsN.le

lemma EBad [NeZero d] (N : ℕ) (hN : 1 ≤ N) (μ : Fin d → ℝ) (hμ0 : ∀ j, 0 < μ j)
    (hμs : ∑ j, μ j = 1) (hNμ : ∀ j, 1 ≤ N * μ j) (ν : ℝ) (hν0 : 0 < ν)
    (hνμ : ∀ j, ν ≤ μ j) :
    (N:ℝ) * ∑ k ∈ Finset.Nat.antidiagonalTuple d N, multW μ k * ∑ j, (2 * Xc N μ k j / μ j) ^ 4
      ≤ 64 * d / (N * ν ^ 2) := by
  have hN0 : (0:ℝ) < N := by exact_mod_cast hN
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  have hb : ∀ j : Fin d, ∑ k ∈ Finset.Nat.antidiagonalTuple d N, (N:ℝ) * (multW μ k * (2 * Xc N μ k j / μ j) ^ 4)
      ≤ 64 / (N * ν ^ 2) := by
    intro j
    have e : ∀ k, (N:ℝ) * (multW μ k * (2 * Xc N μ k j / μ j) ^ 4)
        = (16 * N / μ j ^ 4) * (multW μ k * Xc N μ k j ^ 4) := by
      intro k; have := (hμ0 j).ne'; field_simp; ring
    rw [Finset.sum_congr rfl (fun k _ => e k), ← Finset.mul_sum]
    have h4 := L4 N hN μ hμ0 hμs hNμ j
    have hμj := hμ0 j
    calc (16 * N / μ j ^ 4) * ∑ k ∈ Finset.Nat.antidiagonalTuple d N, multW μ k * Xc N μ k j ^ 4
        ≤ (16 * N / μ j ^ 4) * (4 * μ j ^ 2 / N ^ 2) :=
          mul_le_mul_of_nonneg_left h4 (by positivity)
      _ = 64 / (N * μ j ^ 2) := by field_simp; ring
      _ ≤ 64 / (N * ν ^ 2) := by
          apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
          apply mul_le_mul_of_nonneg_left _ hN0.le
          exact pow_le_pow_left₀ hν0.le (hνμ j) 2
  have := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hb j)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
  calc _ ≤ (d:ℝ) * (64 / (N * ν ^ 2)) := this
    _ = 64 * d / (N * ν ^ 2) := by ring

end WFMFG48C


namespace WFMFG48C

open WFMFG48 WFMFG48I WFMFG48T WFMFG48P WFMFG32

variable {d : ℕ}

/-- The pointwise Taylor/Hölder majorant on the good event. -/
noncomputable def Bk (N : ℕ) (μ : Fin d → ℝ) (K γ' : ℝ) (k : Fin d → ℕ) : ℝ :=
  ∑ j, ∑ m, (|Xc N μ k j * Xc N μ k m| * (2 * K * (∑ e, |Xc N μ k e| ^ (γ' / 2))
          / Real.sqrt (μ m * μ j))
      + |Xc N μ k j * Xc N μ k m| * (2 * K * (|Xc N μ k m| * μ j + |Xc N μ k j| * μ m
          + |Xc N μ k m * Xc N μ k j|) / Real.sqrt (μ m * μ j) ^ 3))

lemma Bk_nonneg (N : ℕ) (μ : Fin d → ℝ) (hμ0 : ∀ j, 0 < μ j) (K γ' : ℝ) (hK0 : 0 ≤ K)
    (k : Fin d → ℕ) : 0 ≤ Bk N μ K γ' k := by
  unfold Bk
  apply Finset.sum_nonneg; intro j _; apply Finset.sum_nonneg; intro m _
  have := hμ0 j; have := hμ0 m
  apply add_nonneg
  · apply mul_nonneg (abs_nonneg _)
    apply div_nonneg _ (Real.sqrt_nonneg _)
    exact mul_nonneg (by positivity) (Finset.sum_nonneg (fun e _ => by positivity))
  · apply mul_nonneg (abs_nonneg _)
    apply div_nonneg _ (by positivity)
    positivity

lemma k_le (N : ℕ) (k : Fin d → ℕ) (hk : k ∈ Finset.Nat.antidiagonalTuple d N) (j : Fin d) :
    k j ≤ N := by
  have := (Finset.Nat.mem_antidiagonalTuple).1 hk
  rw [← this]
  exact Finset.single_le_sum (f := fun i => k i) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)

lemma ksum (N : ℕ) (k : Fin d → ℕ) (hk : k ∈ Finset.Nat.antidiagonalTuple d N) :
    ∑ j, (k j : ℝ) = N := by
  have := (Finset.Nat.mem_antidiagonalTuple).1 hk
  exact_mod_cast this

lemma Xc_abs (N : ℕ) (hN : 1 ≤ N) (μ : Fin d → ℝ) (hμ0 : ∀ j, 0 < μ j) (hμs : ∑ j, μ j = 1)
    (k : Fin d → ℕ) (hk : k ∈ Finset.Nat.antidiagonalTuple d N) (j : Fin d) : |Xc N μ k j| ≤ 1 := by
  have hN0 : (0:ℝ) < N := by exact_mod_cast hN
  have h1 : (k j : ℝ) / N ≤ 1 := by
    rw [div_le_one hN0]; exact_mod_cast k_le N k hk j
  have h0 : 0 ≤ (k j : ℝ) / N := by positivity
  have := mu_le_one μ hμ0 hμs j
  have := hμ0 j
  unfold Xc; rw [abs_le]; constructor <;> linarith

lemma Xc_sum (N : ℕ) (hN : 1 ≤ N) (μ : Fin d → ℝ) (hμs : ∑ j, μ j = 1)
    (k : Fin d → ℕ) (hk : k ∈ Finset.Nat.antidiagonalTuple d N) : ∑ j, Xc N μ k j = 0 := by
  have hN0 : (N:ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  unfold Xc
  rw [Finset.sum_sub_distrib, ← Finset.sum_div, ksum N k hk, hμs, div_self hN0, sub_self]

lemma q_eq (N : ℕ) (μ : Fin d → ℝ) (k : Fin d → ℕ) :
    (fun j => (k j : ℝ) / N) = μ + (1:ℝ) • (fun j => Xc N μ k j) := by
  funext j; simp [Xc]

lemma PW [NeZero d] (N : ℕ) (hN : 1 ≤ N) (μ : Fin d → ℝ) (hμ0 : ∀ j, 0 < μ j)
    (hμs : ∑ j, μ j = 1) (ν : ℝ) (hν0 : 0 < ν) (hνμ : ∀ j, ν ≤ μ j)
    (h : (Fin d → ℝ) → ℝ) (K γ' : ℝ) (hγ0 : 0 < γ')
    (hdiff : ∀ p ∈ simplexInt d, DifferentiableWithinAt ℝ h (affPlane d) p ∧
        ∀ k, DifferentiableWithinAt ℝ (fun q => sD h q k) (affPlane d) p)
    (hK : ∀ j m, ∀ p ∈ simplexInt d, ∀ q ∈ simplexInt d,
      |sD h p j| ≤ K ∧ |Real.sqrt (p j * p m) * sD2 h p j m| ≤ K ∧
      |Real.sqrt (p j * p m) * sD2 h p j m - Real.sqrt (q j * q m) * sD2 h q j m|
        ≤ K * ‖p - q‖ ^ (γ' / 2))
    (hbd : ∀ p ∈ stdSimplex ℝ (Fin d), |h p| ≤ K) (i : Fin d)
    (k : Fin d → ℕ) (hk : k ∈ Finset.Nat.antidiagonalTuple d N) :
    ((k i : ℝ) / (N * μ i)) * |h (fun j => (k j : ℝ) / N) - h μ - ∑ j, Xc N μ k j * sD h μ j
        - (1 / 2) * ∑ j, ∑ m, Xc N μ k j * Xc N μ k m * sD2 h μ m j|
      ≤ (3 / 2) * Bk N μ K γ' k
        + ((2 * K + d * K + d ^ 2 * K) / ν ^ 2) * ∑ j, (2 * Xc N μ k j / μ j) ^ 4 := by
  have hN0 : (0:ℝ) < N := by exact_mod_cast hN
  have hμint : μ ∈ simplexInt d := ⟨hμ0, hμs⟩
  have hK0 : 0 ≤ K := le_trans (abs_nonneg _) (hbd μ ⟨fun j => (hμ0 j).le, hμs⟩)
  have hν1 : ν ≤ 1 := le_trans (hνμ i) (mu_le_one μ hμ0 hμs i)
  set X : Fin d → ℝ := fun j => Xc N μ k j with hXd
  have hXs : ∑ j, X j = 0 := Xc_sum N hN μ hμs k hk
  have hX1 : ∀ j, |X j| ≤ 1 := fun j => Xc_abs N hN μ hμ0 hμs k hk j
  have hρ0 : 0 ≤ (k i : ℝ) / (N * μ i) := by have := hμ0 i; positivity
  have hρX : (k i : ℝ) / (N * μ i) = 1 + X i / μ i := by
    have := (hμ0 i).ne'; simp only [hXd, Xc]; field_simp; ring
  have hBk0 := Bk_nonneg N μ hμ0 K γ' hK0 k
  have hbad0 : 0 ≤ ((2 * K + d * K + d ^ 2 * K) / ν ^ 2) * ∑ j, (2 * X j / μ j) ^ 4 := by
    apply mul_nonneg (by positivity)
    exact Finset.sum_nonneg (fun j _ => by positivity)
  have hsD2 : ∀ j m, |sD2 h μ m j| ≤ K / ν := by
    intro j m
    have h1 := (hK m j μ hμint μ hμint).2.1
    have hb : ν ≤ Real.sqrt (μ m * μ j) := sqrt_ge_nu ν _ _ hν0.le (hνμ m) (hνμ j)
    rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)] at h1
    rw [le_div_iff₀ hν0]
    calc |sD2 h μ m j| * ν ≤ |sD2 h μ m j| * Real.sqrt (μ m * μ j) :=
          mul_le_mul_of_nonneg_left hb (abs_nonneg _)
      _ ≤ K := by linarith
  by_cases hg : ∀ j, |X j| ≤ μ j / 2
  · -- good event: Taylor
    have hmem : ∀ r ∈ Set.Icc (0:ℝ) 1, μ + r • X ∈ simplexInt d := by
      intro r hr
      refine ⟨fun j => ?_, ?_⟩
      · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        have h1 := abs_le.1 (hg j)
        have := hμ0 j
        nlinarith [hr.1, hr.2]
      · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
          ← Finset.mul_sum, hXs, mul_zero, add_zero, hμs]
    have hlow : ∀ r ∈ Set.Icc (0:ℝ) 1, ∀ j, μ j / 2 ≤ (μ + r • X) j := by
      intro r hr j
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have h1 := abs_le.1 (hg j)
      nlinarith [hr.1, hr.2, hμ0 j]
    have hT := taylor2 h μ X hμs hXs (fun r hr => (hdiff _ (hmem r hr)).1)
      (fun r hr j => (hdiff _ (hmem r hr)).2 j) (Bk N μ K γ' k) (by
        intro r hr
        refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
        unfold Bk
        apply Finset.sum_le_sum; intro j _
        refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
        apply Finset.sum_le_sum; intro m _
        set q := μ + r • X with hqd
        have hq := hmem r hr
        set a := Real.sqrt (q m * q j)
        set b := Real.sqrt (μ m * μ j) with hbd'
        have hb0 : 0 < b := Real.sqrt_pos.2 (mul_pos (hμ0 m) (hμ0 j))
        have ha : b / 2 ≤ a := sqrt_half _ _ _ _ (hμ0 m).le (hμ0 j).le (hlow r hr m) (hlow r hr j)
        have hBt : |b * sD2 h μ m j| ≤ K := (hK m j μ hμint μ hμint).2.1
        have hnorm : ‖q - μ‖ ^ (γ' / 2) ≤ ∑ e, |X e| ^ (γ' / 2) := by
          have e1 : q - μ = r • X := by rw [hqd]; abel
          rw [e1, norm_smul, Real.norm_eq_abs, abs_of_nonneg hr.1]
          refine le_trans (Real.rpow_le_rpow (mul_nonneg hr.1 (norm_nonneg _))
            (mul_le_of_le_one_left (norm_nonneg _) hr.2) (by positivity)) ?_
          exact norm_rpow_le_sum X (γ' / 2) (by positivity)
        have hAB : |a * sD2 h q m j - b * sD2 h μ m j| ≤ K * ∑ e, |X e| ^ (γ' / 2) :=
          le_trans (hK m j q hq μ hμint).2.2 (mul_le_mul_of_nonneg_left hnorm hK0)
        have hab : |b ^ 2 - a ^ 2| ≤ |X m| * μ j + |X j| * μ m + |X m * X j| := by
          have hqm : 0 ≤ q m := le_trans (by have := hμ0 m; positivity) (hlow r hr m)
          have hqj : 0 ≤ q j := le_trans (by have := hμ0 j; positivity) (hlow r hr j)
          rw [Real.sq_sqrt (mul_nonneg (hμ0 m).le (hμ0 j).le), Real.sq_sqrt (mul_nonneg hqm hqj)]
          have e2 : μ m * μ j - q m * q j = -(r * (X m * μ j) + r * (X j * μ m) + r ^ 2 * (X m * X j)) := by
            simp only [hqd, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
          rw [e2, abs_neg]
          refine le_trans (abs_add_le _ _) ?_
          refine add_le_add (le_trans (abs_add_le _ _) (add_le_add ?_ ?_)) ?_
          · rw [abs_mul, abs_of_nonneg hr.1, abs_mul, abs_of_pos (hμ0 j)]
            exact mul_le_of_le_one_left (mul_nonneg (abs_nonneg _) (hμ0 j).le) hr.2
          · rw [abs_mul, abs_of_nonneg hr.1, abs_mul, abs_of_pos (hμ0 m)]
            exact mul_le_of_le_one_left (mul_nonneg (abs_nonneg _) (hμ0 m).le) hr.2
          · rw [abs_mul, abs_of_nonneg (sq_nonneg r)]
            exact mul_le_of_le_one_left (abs_nonneg _) (by nlinarith [hr.1, hr.2])
        have hdb := diff_bound (sD2 h q m j) (sD2 h μ m j) a b K _ _ ha hb0 hBt hAB hab
        rw [show X j * X m * (sD2 h q m j - sD2 h μ m j) = (X j * X m) * (sD2 h q m j - sD2 h μ m j)
          by ring, abs_mul]
        calc |X j * X m| * |sD2 h q m j - sD2 h μ m j|
            ≤ |X j * X m| * (2 * (K * ∑ e, |X e| ^ (γ' / 2)) / b
                + 2 * K * (|X m| * μ j + |X j| * μ m + |X m * X j|) / b ^ 3) :=
              mul_le_mul_of_nonneg_left hdb (abs_nonneg _)
          _ = _ := by simp only [hXd]; ring)
    have hq : (fun j => (k j : ℝ) / N) = μ + X := by
      funext j; simp [hXd, Xc]
    rw [hq]
    have hρ32 : (k i : ℝ) / (N * μ i) ≤ 3 / 2 := by
      rw [hρX]
      have := (abs_le.1 (hg i)).2
      have hμi := hμ0 i
      have : X i / μ i ≤ 1 / 2 := by rw [div_le_iff₀ hμi]; linarith
      linarith
    calc (k i : ℝ) / (N * μ i) * |h (μ + X) - h μ - ∑ j, X j * sD h μ j
          - 1 / 2 * ∑ j, ∑ m, X j * X m * sD2 h μ m j|
        ≤ (3 / 2) * Bk N μ K γ' k := mul_le_mul hρ32 hT (abs_nonneg _) (by norm_num)
      _ ≤ _ := le_add_of_nonneg_right hbad0
  · -- bad event: crude bound
    push_neg at hg
    obtain ⟨j0, hj0⟩ := hg
    have hsum1 : 1 ≤ ∑ j, (2 * X j / μ j) ^ 4 := by
      have h1 : 1 ≤ (2 * X j0 / μ j0) ^ 4 := by
        have hμ := hμ0 j0
        have : 1 < |2 * X j0 / μ j0| := by
          rw [abs_div, abs_mul, abs_of_pos hμ, lt_div_iff₀ hμ]; simp; linarith
        have h2 : (2 * X j0 / μ j0) ^ 4 = |2 * X j0 / μ j0| ^ 4 := by
          rw [← abs_pow, abs_of_nonneg (by positivity)]
        rw [h2]; exact one_le_pow₀ this.le
      exact le_trans h1 (Finset.single_le_sum (f := fun j => (2 * X j / μ j) ^ 4)
        (fun j _ => by positivity) (Finset.mem_univ j0))
    have hqs : (fun j => (k j : ℝ) / N) ∈ stdSimplex ℝ (Fin d) := by
      refine ⟨fun j => by positivity, ?_⟩
      have hN' : (N:ℝ) ≠ 0 := hN0.ne'
      simp only; rw [← Finset.sum_div, ksum N k hk, div_self hN']
    have hR : |h (fun j => (k j : ℝ) / N) - h μ - ∑ j, X j * sD h μ j
        - (1 / 2) * ∑ j, ∑ m, X j * X m * sD2 h μ m j| ≤ 2 * K + d * K + d ^ 2 * K / ν := by
      have h1 := hbd _ hqs
      have h2 := hbd μ ⟨fun j => (hμ0 j).le, hμs⟩
      have h3 : |∑ j, X j * sD h μ j| ≤ d * K := by
        refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
        have : ∀ j ∈ Finset.univ, |X j * sD h μ j| ≤ K := by
          intro j _; rw [abs_mul]
          exact le_trans (mul_le_mul (hX1 j) (hK j j μ hμint μ hμint).1 (abs_nonneg _) zero_le_one)
            (by simp)
        have := Finset.sum_le_sum this
        simpa using this
      have h4 : |∑ j, ∑ m, X j * X m * sD2 h μ m j| ≤ d ^ 2 * (K / ν) := by
        refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
        have : ∀ j ∈ Finset.univ, |∑ m, X j * X m * sD2 h μ m j| ≤ d * (K / ν) := by
          intro j _
          refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
          have : ∀ m ∈ Finset.univ, |X j * X m * sD2 h μ m j| ≤ K / ν := by
            intro m _
            rw [abs_mul, abs_mul]
            have hXX : |X j| * |X m| ≤ 1 := by
              have := hX1 j; have := hX1 m
              nlinarith [abs_nonneg (X j), abs_nonneg (X m)]
            calc |X j| * |X m| * |sD2 h μ m j| ≤ 1 * (K / ν) :=
                  mul_le_mul hXX (hsD2 j m) (abs_nonneg _) zero_le_one
              _ = K / ν := one_mul _
          have := Finset.sum_le_sum this
          simpa using this
        have := Finset.sum_le_sum this
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
        nlinarith
      have e : h (fun j => (k j : ℝ) / N) - h μ - ∑ j, X j * sD h μ j
          - (1 / 2) * ∑ j, ∑ m, X j * X m * sD2 h μ m j
          = h (fun j => (k j : ℝ) / N) + (-h μ) + (-∑ j, X j * sD h μ j)
            + (-((1 / 2) * ∑ j, ∑ m, X j * X m * sD2 h μ m j)) := by ring
      rw [e]
      have a1 := abs_add_le (h (fun j => (k j : ℝ) / N) + (-h μ) + (-∑ j, X j * sD h μ j))
        (-((1 / 2) * ∑ j, ∑ m, X j * X m * sD2 h μ m j))
      have a2 := abs_add_le (h (fun j => (k j : ℝ) / N) + (-h μ)) (-∑ j, X j * sD h μ j)
      have a3 := abs_add_le (h (fun j => (k j : ℝ) / N)) (-h μ)
      rw [abs_neg] at a1 a2 a3
      rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 1 / 2)] at a1
      have : (1 / 2) * |∑ j, ∑ m, X j * X m * sD2 h μ m j| ≤ d ^ 2 * K / ν := by
        have : d ^ 2 * (K / ν) = d ^ 2 * K / ν := by ring
        nlinarith [abs_nonneg (∑ j, ∑ m, X j * X m * sD2 h μ m j)]
      linarith
    have hρν : (k i : ℝ) / (N * μ i) ≤ 1 / ν := by
      have hμi := hμ0 i
      rw [div_le_div_iff₀ (by positivity) hν0]
      have hk1 : (k i : ℝ) ≤ N := by exact_mod_cast k_le N k hk i
      nlinarith [hνμ i]
    have hC : (1 / ν) * (2 * K + d * K + d ^ 2 * K / ν) ≤ (2 * K + d * K + d ^ 2 * K) / ν ^ 2 := by
      have h1 : 1 / ν ≤ 1 / ν ^ 2 := by
        apply one_div_le_one_div_of_le (by positivity); nlinarith
      have hd : (0:ℝ) ≤ d := by positivity
      rw [show (1 / ν) * (2 * K + d * K + d ^ 2 * K / ν) = (2 * K + d * K) * (1 / ν) + d ^ 2 * K / ν ^ 2 by
        field_simp]
      rw [show (2 * K + d * K + d ^ 2 * K) / ν ^ 2 = (2 * K + d * K) * (1 / ν ^ 2) + d ^ 2 * K / ν ^ 2 by
        field_simp]
      have : 0 ≤ 2 * K + d * K := by positivity
      nlinarith
    have hCnn : 0 ≤ (2 * K + d * K + d ^ 2 * K) / ν ^ 2 := by positivity
    calc (k i : ℝ) / (N * μ i) * |h (fun j => (k j : ℝ) / N) - h μ - ∑ j, X j * sD h μ j
          - 1 / 2 * ∑ j, ∑ m, X j * X m * sD2 h μ m j|
        ≤ (1 / ν) * (2 * K + d * K + d ^ 2 * K / ν) := mul_le_mul hρν hR (abs_nonneg _) (by positivity)
      _ ≤ (2 * K + d * K + d ^ 2 * K) / ν ^ 2 := hC
      _ ≤ ((2 * K + d * K + d ^ 2 * K) / ν ^ 2) * ∑ j, (2 * X j / μ j) ^ 4 :=
          le_mul_of_one_le_right hCnn hsum1
      _ ≤ _ := le_add_of_nonneg_left (by positivity)

end WFMFG48C


namespace WFMFG48C

open WFMFG48 WFMFG48I WFMFG48T WFMFG48P WFMFG32

variable {d : ℕ}

lemma triple_swap {α : Type*} (S : Finset α) (F : α → Fin d → Fin d → ℝ) :
    ∑ k ∈ S, ∑ j, ∑ m, F k j m = ∑ j, ∑ m, ∑ k ∈ S, F k j m := by
  rw [Finset.sum_comm]; exact Finset.sum_congr rfl (fun j _ => Finset.sum_comm)

lemma sum_swap_weight (μ : Fin d → ℝ) (A : Fin d → Fin d → ℝ) :
    ∑ j, ∑ m, (μ j * (if j = m then 1 else 0) - μ j * μ m) * A m j
      = ∑ j, ∑ m, (μ j * (if j = m then 1 else 0) - μ j * μ m) * A j m := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro j _; apply Finset.sum_congr rfl; intro m _
  by_cases h : j = m
  · subst h; rfl
  · have h' : ¬ m = j := fun e => h e.symm
    simp only [h, h', if_false]; ring

set_option maxHeartbeats 1000000 in
theorem core [NeZero d] (N : ℕ) (hN : 1 ≤ N) (μ : Fin d → ℝ) (hμ0 : ∀ j, 0 < μ j)
    (hμs : ∑ j, μ j = 1) (ν : ℝ) (hν0 : 0 < ν) (hνμ : ∀ j, ν ≤ μ j) (hNν : 1 ≤ N * ν)
    (h : (Fin d → ℝ) → ℝ) (K γ' : ℝ) (hγ0 : 0 < γ') (hγ1 : γ' < 1)
    (hdiff : ∀ p ∈ simplexInt d, DifferentiableWithinAt ℝ h (affPlane d) p ∧
        ∀ k, DifferentiableWithinAt ℝ (fun q => sD h q k) (affPlane d) p)
    (hK : ∀ j m, ∀ p ∈ simplexInt d, ∀ q ∈ simplexInt d,
      |sD h p j| ≤ K ∧ |Real.sqrt (p j * p m) * sD2 h p j m| ≤ K ∧
      |Real.sqrt (p j * p m) * sD2 h p j m - Real.sqrt (q j * q m) * sD2 h q j m|
        ≤ K * ‖p - q‖ ^ (γ' / 2))
    (hbd : ∀ p ∈ stdSimplex ℝ (Fin d), |h p| ≤ K) (i : Fin d) :
    |(N:ℝ) * ∑ k ∈ Finset.Nat.antidiagonalTuple d N,
        multW μ k * (((k i : ℝ) / (N * μ i)) * (h (fun j => (k j : ℝ) / N) - h μ))
      - (∑ j, ((if j = i then 1 else 0) - μ j) * sD h μ j
        + (1 / 2) * ∑ j, ∑ m, (μ j * (if j = m then 1 else 0) - μ j * μ m) * sD2 h μ j m)|
      ≤ 300 * (d:ℝ) ^ 3 * K * ((N:ℝ) ^ (-(γ' / 4)) + 1 / (ν * Real.sqrt N) + 1 / (N * ν ^ 4)) := by
  set S := Finset.Nat.antidiagonalTuple d N with hS
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0:ℝ) < N := by linarith
  have hNne : (N:ℝ) ≠ 0 := hN0.ne'
  have hμ1 : ∀ j, μ j ≤ 1 := mu_le_one μ hμ0 hμs
  have hν1 : ν ≤ 1 := le_trans (hνμ i) (hμ1 i)
  have hNμ : ∀ j, 1 ≤ N * μ j := fun j => le_trans hNν (mul_le_mul_of_nonneg_left (hνμ j) hN0.le)
  have hμint : μ ∈ simplexInt d := ⟨hμ0, hμs⟩
  have hK0 : 0 ≤ K := le_trans (abs_nonneg _) (hbd μ ⟨fun j => (hμ0 j).le, hμs⟩)
  have hw0 : ∀ k, 0 ≤ multW μ k := fun k => multW_nonneg μ (fun j => (hμ0 j).le) k
  have hμi := hμ0 i
  have hμine := hμi.ne'
  -- the remainder
  set R : (Fin d → ℕ) → ℝ := fun k => h (fun j => (k j : ℝ) / N) - h μ
      - ∑ j, Xc N μ k j * sD h μ j - (1 / 2) * ∑ j, ∑ m, Xc N μ k j * Xc N μ k m * sD2 h μ m j
    with hRd
  have hρX : ∀ k : Fin d → ℕ, (k i : ℝ) / (N * μ i) = 1 + Xc N μ k i / μ i := by
    intro k; simp only [Xc]; field_simp; ring
  -- first and second moments against ρ
  have hA1 : ∀ j, (N:ℝ) * ∑ k ∈ S, multW μ k * ((k i : ℝ) / (N * μ i) * Xc N μ k j)
      = (if j = i then 1 else 0) - μ j := by
    intro j
    have e : ∀ k, multW μ k * ((k i : ℝ) / (N * μ i) * Xc N μ k j)
        = multW μ k * Xc N μ k j + (1 / μ i) * (multW μ k * (Xc N μ k i * Xc N μ k j)) := by
      intro k; rw [hρX]; field_simp
    rw [Finset.sum_congr rfl (fun k _ => e k), Finset.sum_add_distrib, ← Finset.mul_sum,
      mom1 N hN μ hμs j, mom2 N hN μ hμs i j]
    by_cases hij : i = j
    · subst hij; simp; field_simp
    · have hji : ¬ j = i := fun e => hij e.symm
      simp [hij, hji]; field_simp
  have hA2 : ∀ j m, (N:ℝ) * ∑ k ∈ S, multW μ k * ((k i : ℝ) / (N * μ i) * (Xc N μ k j * Xc N μ k m))
      = (μ j * (if j = m then 1 else 0) - μ j * μ m)
        + (N / μ i) * ∑ k ∈ S, multW μ k * (Xc N μ k i * (Xc N μ k j * Xc N μ k m)) := by
    intro j m
    have e : ∀ k, multW μ k * ((k i : ℝ) / (N * μ i) * (Xc N μ k j * Xc N μ k m))
        = multW μ k * (Xc N μ k j * Xc N μ k m)
          + (1 / μ i) * (multW μ k * (Xc N μ k i * (Xc N μ k j * Xc N μ k m))) := by
      intro k; rw [hρX]; field_simp
    rw [Finset.sum_congr rfl (fun k _ => e k), Finset.sum_add_distrib, ← Finset.mul_sum,
      mom2 N hN μ hμs j m]
    field_simp
  set T3 : ℝ := (1 / 2) * ∑ j, ∑ m, sD2 h μ m j
      * ((N / μ i) * ∑ k ∈ S, multW μ k * (Xc N μ k i * (Xc N μ k j * Xc N μ k m))) with hT3
  -- the exact identity
  have hid : (N:ℝ) * ∑ k ∈ S, multW μ k * (((k i : ℝ) / (N * μ i)) * (h (fun j => (k j : ℝ) / N) - h μ))
      - (∑ j, ((if j = i then 1 else 0) - μ j) * sD h μ j
        + (1 / 2) * ∑ j, ∑ m, (μ j * (if j = m then 1 else 0) - μ j * μ m) * sD2 h μ j m)
      = T3 + (N:ℝ) * ∑ k ∈ S, multW μ k * ((k i : ℝ) / (N * μ i) * R k) := by
    set A : (Fin d → ℕ) → ℝ := fun k => ∑ j, sD h μ j * (multW μ k * ((k i : ℝ) / (N * μ i) * Xc N μ k j))
      with hAd
    set B : (Fin d → ℕ) → ℝ := fun k => ∑ j, ∑ m, sD2 h μ m j
        * (multW μ k * ((k i : ℝ) / (N * μ i) * (Xc N μ k j * Xc N μ k m))) with hBd
    have hpt : ∀ k, multW μ k * (((k i : ℝ) / (N * μ i)) * (h (fun j => (k j : ℝ) / N) - h μ))
        = A k + (1 / 2) * B k + multW μ k * ((k i : ℝ) / (N * μ i) * R k) := by
      intro k
      have s1 : A k = multW μ k * ((k i : ℝ) / (N * μ i)) * ∑ j, Xc N μ k j * sD h μ j := by
        simp only [hAd, Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring
      have s2 : B k = multW μ k * ((k i : ℝ) / (N * μ i))
          * ∑ j, ∑ m, Xc N μ k j * Xc N μ k m * sD2 h μ m j := by
        simp only [hBd, Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _
        apply Finset.sum_congr rfl; intro m _; ring
      rw [s1, s2]; simp only [hRd]; ring
    have hsA : (N:ℝ) * ∑ k ∈ S, A k = ∑ j, ((if j = i then 1 else 0) - μ j) * sD h μ j := by
      have : (N:ℝ) * ∑ k ∈ S, A k = ∑ j, sD h μ j
          * ((N:ℝ) * ∑ k ∈ S, multW μ k * ((k i : ℝ) / (N * μ i) * Xc N μ k j)) := by
        simp only [hAd]
        rw [Finset.sum_comm]
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro j _; apply Finset.sum_congr rfl; intro k _; ring
      rw [this]; apply Finset.sum_congr rfl; intro j _; rw [hA1 j]; ring
    have hsB : (N:ℝ) * ∑ k ∈ S, B k
        = ∑ j, ∑ m, (μ j * (if j = m then 1 else 0) - μ j * μ m) * sD2 h μ j m + 2 * T3 := by
      have : (N:ℝ) * ∑ k ∈ S, B k = ∑ j, ∑ m, sD2 h μ m j
          * ((N:ℝ) * ∑ k ∈ S, multW μ k * ((k i : ℝ) / (N * μ i) * (Xc N μ k j * Xc N μ k m))) := by
        simp only [hBd]
        rw [triple_swap S (fun k j m => sD2 h μ m j
          * (multW μ k * ((k i : ℝ) / (N * μ i) * (Xc N μ k j * Xc N μ k m))))]
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro j _; apply Finset.sum_congr rfl; intro m _
        apply Finset.sum_congr rfl; intro k _; ring
      rw [this]
      have e2 : ∀ j m, sD2 h μ m j
          * ((N:ℝ) * ∑ k ∈ S, multW μ k * ((k i : ℝ) / (N * μ i) * (Xc N μ k j * Xc N μ k m)))
          = (μ j * (if j = m then 1 else 0) - μ j * μ m) * sD2 h μ m j
            + sD2 h μ m j * ((N / μ i) * ∑ k ∈ S, multW μ k * (Xc N μ k i * (Xc N μ k j * Xc N μ k m))) := by
        intro j m; rw [hA2 j m]; ring
      simp only [e2, Finset.sum_add_distrib]
      rw [sum_swap_weight μ (fun a b => sD2 h μ a b), hT3]
      ring
    rw [Finset.sum_congr rfl (fun k _ => hpt k), Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, mul_add, mul_add, hsA]
    have : (N:ℝ) * ((1 / 2) * ∑ k ∈ S, B k) = (1 / 2) * ((N:ℝ) * ∑ k ∈ S, B k) := by ring
    rw [this, hsB]
    ring
  rw [hS] at hid
  rw [hid]
  -- bound T3
  have hT3b : |T3| ≤ (d:ℝ) ^ 2 * K * (1 / (ν * Real.sqrt N)) := by
    have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
    have hsμ : ν ≤ Real.sqrt (μ i) := by
      rw [Real.le_sqrt hν0.le hμi.le]; nlinarith [hνμ i]
    have hkey : Real.sqrt (μ i / N) / μ i ≤ 1 / (ν * Real.sqrt N) := by
      rw [Real.sqrt_div' _ hN0.le]
      have hsμ0 : 0 < Real.sqrt (μ i) := Real.sqrt_pos.2 hμi
      have : Real.sqrt (μ i) / Real.sqrt N / μ i = 1 / (Real.sqrt (μ i) * Real.sqrt N) := by
        have := Real.mul_self_sqrt hμi.le
        field_simp
        nlinarith
      rw [this]
      apply one_div_le_one_div_of_le (by positivity)
      exact mul_le_mul_of_nonneg_right hsμ hsN.le
    have hterm : ∀ j m, |sD2 h μ m j
        * ((N / μ i) * ∑ k ∈ S, multW μ k * (Xc N μ k i * (Xc N μ k j * Xc N μ k m)))|
        ≤ 2 * K * (1 / (ν * Real.sqrt N)) := by
      intro j m
      set b := Real.sqrt (μ m * μ j)
      have hb0 : 0 < b := Real.sqrt_pos.2 (mul_pos (hμ0 m) (hμ0 j))
      have hbb : Real.sqrt (μ j * μ m) = b := by rw [mul_comm]
      have h1 := (hK m j μ hμint μ hμint).2.1
      rw [abs_mul, abs_of_pos hb0] at h1
      have hs2 : |sD2 h μ m j| ≤ K / b := by rw [le_div_iff₀ hb0]; linarith
      have hE : |∑ k ∈ S, multW μ k * (Xc N μ k i * (Xc N μ k j * Xc N μ k m))|
          ≤ Real.sqrt (μ i / N) * (2 * b / N) := by
        refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
        have := Lt N hN μ hμ0 hμs hNμ i j m
        rw [hbb] at this
        refine le_trans (le_of_eq ?_) this
        apply Finset.sum_congr rfl; intro k _
        rw [abs_mul, abs_of_nonneg (hw0 k)]
      rw [abs_mul, abs_mul, abs_of_pos (by positivity : (0:ℝ) < N / μ i)]
      calc |sD2 h μ m j| * (N / μ i * |∑ k ∈ S, multW μ k * (Xc N μ k i * (Xc N μ k j * Xc N μ k m))|)
          ≤ (K / b) * (N / μ i * (Real.sqrt (μ i / N) * (2 * b / N))) :=
            mul_le_mul hs2 (mul_le_mul_of_nonneg_left hE (by positivity)) (by positivity)
              (by positivity)
        _ = 2 * K * (Real.sqrt (μ i / N) / μ i) := by field_simp
        _ ≤ 2 * K * (1 / (ν * Real.sqrt N)) := mul_le_mul_of_nonneg_left hkey (by positivity)
    rw [hT3, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 1 / 2)]
    have hs : |∑ j, ∑ m, sD2 h μ m j
        * ((N / μ i) * ∑ k ∈ S, multW μ k * (Xc N μ k i * (Xc N μ k j * Xc N μ k m)))|
        ≤ (d:ℝ) ^ 2 * (2 * K * (1 / (ν * Real.sqrt N))) := by
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      have : ∀ j ∈ Finset.univ, |∑ m, sD2 h μ m j
          * ((N / μ i) * ∑ k ∈ S, multW μ k * (Xc N μ k i * (Xc N μ k j * Xc N μ k m)))|
          ≤ (d:ℝ) * (2 * K * (1 / (ν * Real.sqrt N))) := by
        intro j _
        refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
        have := Finset.sum_le_sum (fun m (_ : m ∈ Finset.univ) => hterm j m)
        simpa using this
      have := Finset.sum_le_sum this
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
      nlinarith
    nlinarith
  -- bound the remainder
  have hRb : |(N:ℝ) * ∑ k ∈ S, multW μ k * ((k i : ℝ) / (N * μ i) * R k)|
      ≤ (3 / 2) * ((d:ℝ) ^ 2 * (4 * K * d * (N:ℝ) ^ (-(γ' / 4)) + 16 * K / (ν * Real.sqrt N)))
        + ((2 * K + d * K + d ^ 2 * K) / ν ^ 2) * (64 * d / (N * ν ^ 2)) := by
    have hpw : ∀ k ∈ S, |multW μ k * ((k i : ℝ) / (N * μ i) * R k)|
        ≤ multW μ k * ((3 / 2) * Bk N μ K γ' k
          + ((2 * K + d * K + d ^ 2 * K) / ν ^ 2) * ∑ j, (2 * Xc N μ k j / μ j) ^ 4) := by
      intro k hk
      rw [abs_mul, abs_of_nonneg (hw0 k), abs_mul,
        abs_of_nonneg (by positivity : (0:ℝ) ≤ (k i : ℝ) / (N * μ i))]
      exact mul_le_mul_of_nonneg_left
        (PW N hN μ hμ0 hμs ν hν0 hνμ h K γ' hγ0 hdiff hK hbd i k hk) (hw0 k)
    rw [abs_mul, abs_of_pos hN0]
    refine le_trans (mul_le_mul_of_nonneg_left (le_trans (Finset.abs_sum_le_sum_abs _ _)
      (Finset.sum_le_sum hpw)) hN0.le) ?_
    simp only [mul_add, Finset.sum_add_distrib]
    have hB1 : (N:ℝ) * ∑ k ∈ S, multW μ k * ((3 / 2) * Bk N μ K γ' k)
        ≤ (3 / 2) * ((d:ℝ) ^ 2 * (4 * K * d * (N:ℝ) ^ (-(γ' / 4)) + 16 * K / (ν * Real.sqrt N))) := by
      have e : (N:ℝ) * ∑ k ∈ S, multW μ k * ((3 / 2) * Bk N μ K γ' k)
          = (3 / 2) * ∑ j, ∑ m, ((N:ℝ) * ∑ k ∈ S, multW μ k *
              (|Xc N μ k j * Xc N μ k m| * (2 * K * (∑ e, |Xc N μ k e| ^ (γ' / 2))
                / Real.sqrt (μ m * μ j)))
            + (N:ℝ) * ∑ k ∈ S, multW μ k *
              (|Xc N μ k j * Xc N μ k m| * (2 * K * (|Xc N μ k m| * μ j + |Xc N μ k j| * μ m
                + |Xc N μ k m * Xc N μ k j|) / Real.sqrt (μ m * μ j) ^ 3))) := by
        set F : (Fin d → ℕ) → Fin d → Fin d → ℝ := fun k j m =>
          (N:ℝ) * (multW μ k * (|Xc N μ k j * Xc N μ k m| * (2 * K * (∑ e, |Xc N μ k e| ^ (γ' / 2))
                / Real.sqrt (μ m * μ j))))
          + (N:ℝ) * (multW μ k * (|Xc N μ k j * Xc N μ k m| * (2 * K * (|Xc N μ k m| * μ j
                + |Xc N μ k j| * μ m + |Xc N μ k m * Xc N μ k j|) / Real.sqrt (μ m * μ j) ^ 3))) with hF
        have p1 : ∀ k, (N:ℝ) * (multW μ k * ((3 / 2) * Bk N μ K γ' k)) = (3 / 2) * ∑ j, ∑ m, F k j m := by
          intro k
          simp only [Bk, hF, Finset.mul_sum]
          apply Finset.sum_congr rfl; intro j _; apply Finset.sum_congr rfl; intro m _; ring
        rw [Finset.mul_sum, Finset.sum_congr rfl (fun k _ => p1 k), ← Finset.mul_sum, triple_swap]
        congr 1
        apply Finset.sum_congr rfl; intro j _; apply Finset.sum_congr rfl; intro m _
        simp only [hF, Finset.sum_add_distrib, ← Finset.mul_sum]
      rw [e]
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      have hjm : ∀ j m, (N:ℝ) * ∑ k ∈ S, multW μ k *
              (|Xc N μ k j * Xc N μ k m| * (2 * K * (∑ e, |Xc N μ k e| ^ (γ' / 2))
                / Real.sqrt (μ m * μ j)))
            + (N:ℝ) * ∑ k ∈ S, multW μ k *
              (|Xc N μ k j * Xc N μ k m| * (2 * K * (|Xc N μ k m| * μ j + |Xc N μ k j| * μ m
                + |Xc N μ k m * Xc N μ k j|) / Real.sqrt (μ m * μ j) ^ 3))
          ≤ 4 * K * d * (N:ℝ) ^ (-(γ' / 4)) + 16 * K / (ν * Real.sqrt N) :=
        fun j m => add_le_add (EB1 N hN μ hμ0 hμs hNμ γ' K hγ0 hγ1 hK0 j m)
          (EB2 N hN μ hμ0 hμs hNμ K ν hK0 hν0 hνμ j m)
      have := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) =>
        Finset.sum_le_sum (fun m (_ : m ∈ Finset.univ) => hjm j m))
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
      calc _ ≤ (d:ℝ) * ((d:ℝ) * (4 * K * d * (N:ℝ) ^ (-(γ' / 4)) + 16 * K / (ν * Real.sqrt N))) := this
        _ = _ := by ring
    have hB2 : (N:ℝ) * ∑ k ∈ S, multW μ k * (((2 * K + d * K + d ^ 2 * K) / ν ^ 2)
          * ∑ j, (2 * Xc N μ k j / μ j) ^ 4)
        ≤ ((2 * K + d * K + d ^ 2 * K) / ν ^ 2) * (64 * d / (N * ν ^ 2)) := by
      have e : (N:ℝ) * ∑ k ∈ S, multW μ k * (((2 * K + d * K + d ^ 2 * K) / ν ^ 2)
          * ∑ j, (2 * Xc N μ k j / μ j) ^ 4)
          = ((2 * K + d * K + d ^ 2 * K) / ν ^ 2)
            * ((N:ℝ) * ∑ k ∈ S, multW μ k * ∑ j, (2 * Xc N μ k j / μ j) ^ 4) := by
        rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl; intro k _; ring
      rw [e]
      exact mul_le_mul_of_nonneg_left (EBad N hN μ hμ0 hμs hNμ ν hν0 hνμ) (by positivity)
    linarith
  -- combine
  have hd1 : (1:ℝ) ≤ d := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne d)
  set P1 := (N:ℝ) ^ (-(γ' / 4)) with hP1
  set P2 := 1 / (ν * Real.sqrt N) with hP2
  set P3 := 1 / (N * ν ^ 4) with hP3
  have hP10 : 0 ≤ P1 := by positivity
  have hP20 : 0 ≤ P2 := by positivity
  have hP30 : 0 ≤ P3 := by positivity
  have e16 : 16 * K / (ν * Real.sqrt N) = 16 * K * P2 := by rw [hP2]; ring
  have e64 : ((2 * K + d * K + d ^ 2 * K) / ν ^ 2) * (64 * d / (N * ν ^ 2))
      = 64 * d * (2 + d + d ^ 2) * K * P3 := by rw [hP3]; field_simp
  rw [e16, e64] at hRb
  have hd2 : (d:ℝ) ^ 2 ≤ d ^ 3 := by nlinarith
  have hd3 : (d:ℝ) * (2 + d + d ^ 2) ≤ 4 * d ^ 3 := by nlinarith
  have hKP2 : 0 ≤ K * P2 := mul_nonneg hK0 hP20
  have hKP1 : 0 ≤ K * P1 := mul_nonneg hK0 hP10
  have hKP3 : 0 ≤ K * P3 := mul_nonneg hK0 hP30
  have i1 : (d:ℝ) ^ 2 * (K * P2) ≤ d ^ 3 * (K * P2) := mul_le_mul_of_nonneg_right hd2 hKP2
  have i3 : (d:ℝ) * (2 + d + d ^ 2) * (K * P3) ≤ 4 * d ^ 3 * (K * P3) :=
    mul_le_mul_of_nonneg_right hd3 hKP3
  have hsum : |T3 + (N:ℝ) * ∑ k ∈ S, multW μ k * ((k i : ℝ) / (N * μ i) * R k)|
      ≤ (d:ℝ) ^ 2 * K * P2
        + ((3 / 2) * ((d:ℝ) ^ 2 * (4 * K * d * P1 + 16 * K * P2)) + 64 * d * (2 + d + d ^ 2) * K * P3) :=
    le_trans (abs_add_le _ _) (add_le_add hT3b hRb)
  refine le_trans hsum ?_
  have hd30 : (0:ℝ) ≤ d ^ 3 := by positivity
  nlinarith [mul_nonneg hd30 hKP1, mul_nonneg hd30 hKP2, mul_nonneg hd30 hKP3]

end WFMFG48C


namespace WFMFG48M

open WFMFG48 WFMFG48I WFMFG48T WFMFG48P WFMFG48C WFMFG32

variable {d : ℕ}

lemma bound_closure [NeZero d] (f : (Fin d → ℝ) → ℝ) (hc : ContinuousOn f (stdSimplex ℝ (Fin d)))
    (K : ℝ) (hK : ∀ p ∈ simplexInt d, |f p| ≤ K) : ∀ p ∈ stdSimplex ℝ (Fin d), |f p| ≤ K := by
  intro p hp
  have hd0 : (0:ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  set c : Fin d → ℝ := fun _ => 1 / (d:ℝ) with hcd
  set g : ℝ → (Fin d → ℝ) := fun s => (1 - s) • p + s • c with hg
  have hgc : Continuous g := by fun_prop
  have hg0 : g 0 = p := by simp [hg]
  have hmem : ∀ s ∈ Set.Ioo (0:ℝ) 1, g s ∈ simplexInt d := by
    intro s hs
    refine ⟨fun j => ?_, ?_⟩
    · simp only [hg, hcd, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have := hp.1 j
      have : 0 < s * (1 / (d:ℝ)) := mul_pos hs.1 (by positivity)
      nlinarith [hs.2]
    · simp only [hg, hcd, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
        ← Finset.mul_sum, hp.2, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp; ring
  have hT : Filter.Tendsto g (nhdsWithin 0 (Set.Ioi 0)) (nhdsWithin p (stdSimplex ℝ (Fin d))) := by
    apply tendsto_nhdsWithin_iff.2
    refine ⟨?_, ?_⟩
    · rw [← hg0]; exact hgc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [Ioo_mem_nhdsGT (zero_lt_one : (0:ℝ) < 1)] with s hs
      exact ⟨fun j => (hmem s hs).1 j |>.le, (hmem s hs).2⟩
  have hlim := ((continuous_abs.tendsto _).comp ((hc p hp).tendsto.comp hT))
  refine le_of_tendsto hlim ?_
  filter_upwards [Ioo_mem_nhdsGT (zero_lt_one : (0:ℝ) < 1)] with s hs
  exact hK _ (hmem s hs)

lemma empQ_reweight {N : ℕ} (hN : 1 ≤ N) (x : Fin N → Fin d) (y : Fin N → ℚ)
    (hpos : ∀ j, empQ x y j ≠ 0) (k : Fin d → ℕ) (j : Fin d) :
    empQ x (reweight x y k) j = (k j : ℚ) / N := by
  have hN0 : (N:ℚ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hej := hpos j
  have e1 : ∀ l, (if x l = j then reweight x y k l else 0)
      = ((k j : ℚ) / (N * empQ x y j)) * (if x l = j then y l else 0) := by
    intro l
    split_ifs with h
    · simp only [reweight, ratioQ, h, hej, if_false]; ring
    · ring
  have hsum : ∑ l, (if x l = j then y l else 0) = N * empQ x y j := by
    unfold empQ; field_simp
  unfold empQ
  rw [Finset.sum_congr rfl (fun l _ => e1 l), ← Finset.mul_sum, hsum]
  field_simp

theorem lemma48 (γ' ϵ : ℝ) (hγ0 : 0 < γ') (hγ1 : γ' < 1) (hϵ0 : 0 < ϵ) (hϵ1 : ϵ < 1 / 4) :
    ∃ η : ℝ, 0 < η ∧
    ∀ (d : ℕ) [NeZero d] (T : ℝ), 0 < T →
    ∀ U : Fin d → ℝ → (Fin d → ℝ) → ℝ, WFReg γ' T U →
    ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
    ∀ (l : Fin N) (t : ℝ) (x : Fin N → Fin d) (y : Fin N → ℚ),
      t ∈ Set.Icc 0 T → y ∈ Yset N → TN ϵ x y → 0 < y l →
      |(1 / (y l : ℝ)) * N
            * multE N (empMeas x y) (fun k => uN U l t x (reweight x y k) - uN U l t x y)
          - ∑ j, ((if j = x l then 1 else 0) - empMeas x y j) * sD (U (x l) t) (empMeas x y) j
          - (1 / 2) * ∑ j, ∑ k,
              (empMeas x y j * (if j = k then 1 else 0) - empMeas x y j * empMeas x y k)
                * sD2 (U (x l) t) (empMeas x y) j k| ≤
        C / (N : ℝ) ^ η := by
  set η := min (γ' / 4) (min (1 / 2 - ϵ) (1 - 4 * ϵ)) with hηd
  have hη : 0 < η := lt_min (by linarith) (lt_min (by linarith) (by linarith))
  refine ⟨η, hη, ?_⟩
  intro d _ T hT U hU
  obtain ⟨hUc, hUd, K, hK⟩ := hU
  refine ⟨900 * (d:ℝ) ^ 3 * K, ?_⟩
  intro N hN l t x y ht hy hTN hyl
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0:ℝ) < N := by linarith
  set μ := empMeas x y with hμd
  set i := x l with hid
  set ν : ℝ := (N:ℝ) ^ (-ϵ) with hνd
  have hν0 : 0 < ν := Real.rpow_pos_of_pos hN0 _
  have hνμ : ∀ j, ν ≤ μ j := hTN.1
  have hμ0 : ∀ j, 0 < μ j := fun j => lt_of_lt_of_le hν0 (hνμ j)
  have hμs : ∑ j, μ j = 1 := (emp_std hN x y hy).2
  have hNν : 1 ≤ (N:ℝ) * ν := by
    have : (N:ℝ) * ν = (N:ℝ) ^ (1 - ϵ) := by
      rw [hνd, Real.rpow_sub hN0, Real.rpow_one, Real.rpow_neg hN0.le, div_eq_mul_inv]
    rw [this]; exact Real.one_le_rpow hN1 (by linarith)
  set h := U i t with hhd
  have hdiff : ∀ p ∈ simplexInt d, DifferentiableWithinAt ℝ h (affPlane d) p ∧
      ∀ k, DifferentiableWithinAt ℝ (fun q => sD h q k) (affPlane d) p :=
    fun p hp => hUd i t ht p hp
  have hKc : ∀ j m, ∀ p ∈ simplexInt d, ∀ q ∈ simplexInt d,
      |sD h p j| ≤ K ∧ |Real.sqrt (p j * p m) * sD2 h p j m| ≤ K ∧
      |Real.sqrt (p j * p m) * sD2 h p j m - Real.sqrt (q j * q m) * sD2 h q j m|
        ≤ K * ‖p - q‖ ^ (γ' / 2) := by
    intro j m p hp q hq
    have := hK i j m t ht p hp q hq
    exact ⟨this.2.1, this.2.2.2.1, this.2.2.2.2⟩
  have hcont : ContinuousOn h (stdSimplex ℝ (Fin d)) := by
    have := (hUc i).comp (continuous_const.prodMk continuous_id).continuousOn
      (fun p hp => (⟨ht, hp⟩ : (t, p) ∈ Set.Icc 0 T ×ˢ stdSimplex ℝ (Fin d)))
    exact this
  have hbd : ∀ p ∈ stdSimplex ℝ (Fin d), |h p| ≤ K :=
    bound_closure h hcont K (fun p hp => (hK i i i t ht p hp p hp).1)
  have hcore := core N hN μ hμ0 hμs ν hν0 hνμ hNν h K γ' hγ0 hγ1 hdiff hKc hbd i
  -- identify the left-hand side
  have hposQ : ∀ j, empQ x y j ≠ 0 := by
    intro j
    have := hμ0 j
    simp only [hμd, empMeas] at this
    exact_mod_cast this.ne'
  have hrw : ∀ k, empMeas x (reweight x y k) = fun j => (k j : ℝ) / N := by
    intro k; funext j
    simp only [empMeas]; rw [empQ_reweight hN x y hposQ k j]; push_cast; ring
  have hratio : ∀ k, ((ratioQ x y k l : ℚ) : ℝ) = (k i : ℝ) / (N * μ i) := by
    intro k
    rw [ratio_cast]
    simp only [hposQ (x l), if_false, hid, hμd]
  have hyl' : (y l : ℝ) ≠ 0 := by exact_mod_cast hyl.ne'
  have hwρ : ∑ k ∈ Finset.Nat.antidiagonalTuple d N, multW μ k * ((k i : ℝ) / (N * μ i)) = 1 := by
    have := noise_mass hN x y hy l
    simp only [← hμd] at this
    rw [← this]
    apply Finset.sum_congr rfl; intro k _; rw [hratio]
  have hw1 : ∑ k ∈ Finset.Nat.antidiagonalTuple d N, multW μ k = 1 := w_sum N μ hμs
  have hLHS : (1 / (y l : ℝ)) * N
        * multE N μ (fun k => uN U l t x (reweight x y k) - uN U l t x y)
      = (N:ℝ) * ∑ k ∈ Finset.Nat.antidiagonalTuple d N,
          multW μ k * (((k i : ℝ) / (N * μ i)) * (h (fun j => (k j : ℝ) / N) - h μ)) := by
    have e : ∀ k, multW μ k * (uN U l t x (reweight x y k) - uN U l t x y)
        = (y l : ℝ) * (multW μ k * (((k i : ℝ) / (N * μ i)) * (h (fun j => (k j : ℝ) / N) - h μ)))
          + (y l : ℝ) * h μ * (multW μ k * ((k i : ℝ) / (N * μ i)) - multW μ k) := by
      intro k
      unfold uN zN
      rw [hrw k]
      have : ((reweight x y k l : ℚ) : ℝ) = (y l : ℝ) * (k i : ℝ) / (N * μ i) := by
        unfold reweight; push_cast; rw [hratio]; ring
      rw [this, ← hhd, ← hμd]
      ring
    unfold multE
    rw [Finset.sum_congr rfl (fun k _ => e k), Finset.sum_add_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum, Finset.sum_sub_distrib, hwρ, hw1]
    field_simp
    ring
  rw [hLHS, sub_sub]
  refine le_trans hcore ?_
  -- exponents
  have hK0 : 0 ≤ K := le_trans (abs_nonneg _) (hbd μ ⟨fun j => (hμ0 j).le, hμs⟩)
  have hpowη : ∀ a : ℝ, η ≤ a → (N:ℝ) ^ (-a) ≤ (N:ℝ) ^ (-η) := fun a ha =>
    Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have p1 : (N:ℝ) ^ (-(γ' / 4)) ≤ (N:ℝ) ^ (-η) := hpowη _ (min_le_left _ _)
  have p2 : 1 / (ν * Real.sqrt N) ≤ (N:ℝ) ^ (-η) := by
    have : 1 / (ν * Real.sqrt N) = (N:ℝ) ^ (-(1 / 2 - ϵ)) := by
      rw [hνd, Real.sqrt_eq_rpow, ← Real.rpow_add hN0, one_div, ← Real.rpow_neg hN0.le]
      ring_nf
    rw [this]; exact hpowη _ (le_trans (min_le_right _ _) (min_le_left _ _))
  have p3 : 1 / ((N:ℝ) * ν ^ 4) ≤ (N:ℝ) ^ (-η) := by
    have : 1 / ((N:ℝ) * ν ^ 4) = (N:ℝ) ^ (-(1 - 4 * ϵ)) := by
      have hν4 : ν ^ 4 = (N:ℝ) ^ (-(4 * ϵ)) := by
        rw [hνd, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; ring_nf
      have h2 : (N:ℝ) * ν ^ 4 = (N:ℝ) ^ (1 - 4 * ϵ) := by
        rw [hν4, show (1:ℝ) - 4 * ϵ = 1 + (-(4 * ϵ)) by ring, Real.rpow_add hN0, Real.rpow_one]
      rw [h2, one_div, ← Real.rpow_neg hN0.le]
    rw [this]; exact hpowη _ (le_trans (min_le_right _ _) (min_le_right _ _))
  have hC0 : 0 ≤ 300 * (d:ℝ) ^ 3 * K := by positivity
  have hfin : 300 * (d:ℝ) ^ 3 * K * ((N:ℝ) ^ (-(γ' / 4)) + 1 / (ν * Real.sqrt N) + 1 / (N * ν ^ 4))
      ≤ 300 * (d:ℝ) ^ 3 * K * (3 * (N:ℝ) ^ (-η)) :=
    mul_le_mul_of_nonneg_left (by linarith) hC0
  refine le_trans hfin (le_of_eq ?_)
  rw [Real.rpow_neg hN0.le]
  field_simp
  ring

end WFMFG48M

theorem solution (γ' ϵ : ℝ) (hγ0 : 0 < γ') (hγ1 : γ' < 1) (hϵ0 : 0 < ϵ) (hϵ1 : ϵ < 1 / 4) :
    ∃ η : ℝ, 0 < η ∧
    ∀ (d : ℕ) [NeZero d] (T : ℝ), 0 < T →
    ∀ U : Fin d → ℝ → (Fin d → ℝ) → ℝ, WFReg γ' T U →
    ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
    ∀ (l : Fin N) (t : ℝ) (x : Fin N → Fin d) (y : Fin N → ℚ),
      t ∈ Set.Icc 0 T → y ∈ Yset N → TN ϵ x y → 0 < y l →
      |(1 / (y l : ℝ)) * N
            * multE N (empMeas x y) (fun k => uN U l t x (reweight x y k) - uN U l t x y)
          - ∑ j, ((if j = x l then 1 else 0) - empMeas x y j) * sD (U (x l) t) (empMeas x y) j
          - (1 / 2) * ∑ j, ∑ k,
              (empMeas x y j * (if j = k then 1 else 0) - empMeas x y j * empMeas x y k)
                * sD2 (U (x l) t) (empMeas x y) j k| ≤
        C / (N : ℝ) ^ η :=
  WFMFG48M.lemma48 γ' ϵ hγ0 hγ1 hϵ0 hϵ1
