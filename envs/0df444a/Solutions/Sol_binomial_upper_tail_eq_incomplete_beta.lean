-- Prove2me | solution 1 for binomial_upper_tail_eq_incomplete_beta
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-06-21T14:17:48.156056+00:00
-- url     : https://prove2.me/submissions/d80f3114-3509-4062-8d4e-a0c0eda60a58

import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Algebra.BigOperators.Intervals
import Definitions.Def_matrix_completion_fixed_cardinality

open scoped BigOperators
open Finset
open MatrixCompletion

namespace IncBeta

-- A_k(x) = N * C(N-1,k-1) * x^(k-1) * (1-x)^(N-k)
noncomputable def Aterm (N k : ℕ) (x : ℝ) : ℝ :=
  (N : ℝ) * (Nat.choose (N-1) (k-1) : ℝ) * x ^ (k-1) * (1 - x) ^ (N - k)
-- B_k(x) = N * C(N-1,k) * x^k * (1-x)^(N-1-k)
noncomputable def Bterm (N k : ℕ) (x : ℝ) : ℝ :=
  (N : ℝ) * (Nat.choose (N-1) k : ℝ) * x ^ k * (1 - x) ^ (N - 1 - k)

theorem term_deriv (N k : ℕ) (hk1 : 1 ≤ k) (hkN : k ≤ N) (x : ℝ) :
    HasDerivAt (fun p : ℝ => (Nat.choose N k : ℝ) * p ^ k * (1 - p) ^ (N - k))
      (Aterm N k x - Bterm N k x) x := by
  have h1 : HasDerivAt (fun p : ℝ => p ^ k) ((k : ℝ) * x ^ (k-1)) x := by
    simpa using hasDerivAt_pow k x
  have h2 : HasDerivAt (fun p : ℝ => (1 - p) ^ (N-k)) (-(((N-k : ℕ) : ℝ) * (1-x)^(N-k-1))) x := by
    have hb : HasDerivAt (fun p : ℝ => (1 - p)) (-1) x := by
      simpa using (hasDerivAt_id x).const_sub 1
    have := (hasDerivAt_pow (N-k) (1 - x)).comp x hb
    exact this.congr_deriv (by ring)
  have hmul : HasDerivAt (fun p : ℝ => p ^ k * (1 - p) ^ (N-k))
      ((k : ℝ) * x ^ (k-1) * (1-x)^(N-k) + x^k * (-(((N-k:ℕ):ℝ) * (1-x)^(N-k-1)))) x := h1.mul h2
  have hp := hmul.const_mul (Nat.choose N k : ℝ)
  have hfun : (fun p : ℝ => (Nat.choose N k : ℝ) * (p ^ k * (1 - p) ^ (N - k)))
      = (fun p : ℝ => (Nat.choose N k : ℝ) * p ^ k * (1 - p) ^ (N - k)) := by
    funext p; ring
  rw [hfun] at hp
  refine hp.congr_deriv ?_
  have e1 : (N : ℝ) * (Nat.choose (N-1) (k-1) : ℝ) = (Nat.choose N k : ℝ) * (k : ℝ) := by
    have := Nat.add_one_mul_choose_eq (N-1) (k-1)
    have hk : (k-1)+1 = k := by omega
    have hN' : (N-1)+1 = N := by omega
    rw [hk, hN'] at this
    have := congrArg (Nat.cast : ℕ → ℝ) this
    push_cast at this
    linarith [this]
  have e2 : (N : ℝ) * (Nat.choose (N-1) k : ℝ) = (Nat.choose N k : ℝ) * ((N - k : ℕ) : ℝ) := by
    have := Nat.choose_mul_succ_eq (N-1) k
    have hN' : (N-1)+1 = N := by omega
    rw [hN'] at this
    have := congrArg (Nat.cast : ℕ → ℝ) this
    push_cast at this
    linarith [this]
  have he : N - 1 - k = N - k - 1 := by omega
  simp only [Aterm, Bterm, he]
  rw [e1, e2]
  ring

theorem Bterm_eq_Aterm_succ (N k : ℕ) (x : ℝ) : Bterm N k x = Aterm N (k+1) x := by
  unfold Aterm Bterm
  have h1 : k + 1 - 1 = k := by omega
  rw [h1]
  congr 2
  omega

theorem Aterm_top_zero (N : ℕ) (hN : 1 ≤ N) (x : ℝ) : Aterm N (N+1) x = 0 := by
  unfold Aterm
  have hz : Nat.choose (N-1) (N+1-1) = 0 := by
    apply Nat.choose_eq_zero_of_lt; omega
  rw [hz]; simp

theorem tail_deriv (N m : ℕ) (h : m < N) (x : ℝ) :
    HasDerivAt (fun p : ℝ => ∑ k ∈ Finset.Ico (m+1) (N+1),
        (Nat.choose N k : ℝ) * p ^ k * (1 - p) ^ (N - k))
      ((N : ℝ) * (Nat.choose (N-1) m : ℝ) * x ^ m * (1 - x) ^ (N - 1 - m)) x := by
  have hsum : HasDerivAt (fun p : ℝ => ∑ k ∈ Finset.Ico (m+1) (N+1),
        (Nat.choose N k : ℝ) * p ^ k * (1 - p) ^ (N - k))
      (∑ k ∈ Finset.Ico (m+1) (N+1), (Aterm N k x - Bterm N k x)) x := by
    have hh := HasDerivAt.sum (u := Finset.Ico (m+1) (N+1))
      (A := fun k => fun p : ℝ => (Nat.choose N k : ℝ) * p ^ k * (1 - p) ^ (N - k))
      (A' := fun k => Aterm N k x - Bterm N k x) (x := x)
      (fun k hk => by rw [Finset.mem_Ico] at hk; exact term_deriv N k (by omega) (by omega) x)
    have hfe : (fun p : ℝ => ∑ k ∈ Finset.Ico (m+1) (N+1),
        (Nat.choose N k : ℝ) * p ^ k * (1 - p) ^ (N - k))
        = (∑ k ∈ Finset.Ico (m+1) (N+1), fun p : ℝ =>
            (Nat.choose N k : ℝ) * p ^ k * (1 - p) ^ (N - k)) := by
      funext p
      simp only [Finset.sum_apply]
    rw [hfe]
    exact hh
  have htel : (∑ k ∈ Finset.Ico (m+1) (N+1), (Aterm N k x - Bterm N k x))
      = (N : ℝ) * (Nat.choose (N-1) m : ℝ) * x ^ m * (1 - x) ^ (N - 1 - m) := by
    have : (∑ k ∈ Finset.Ico (m+1) (N+1), (Aterm N k x - Bterm N k x))
        = ∑ k ∈ Finset.Ico (m+1) (N+1), (Aterm N k x - Aterm N (k+1) x) := by
      apply Finset.sum_congr rfl; intro k _; rw [Bterm_eq_Aterm_succ]
    rw [this]
    rw [Finset.sum_Ico_eq_sum_range]
    have hlen : N + 1 - (m + 1) = N - m := by omega
    rw [hlen]
    have hcongr : (∑ i ∈ Finset.range (N-m), (Aterm N (m+1+i) x - Aterm N (m+1+i+1) x))
        = ∑ i ∈ Finset.range (N-m), ((fun j => Aterm N (m+1+j) x) i - (fun j => Aterm N (m+1+j) x) (i+1)) := by
      apply Finset.sum_congr rfl; intro i _; simp only []; ring_nf
    rw [hcongr, Finset.sum_range_sub' (fun j => Aterm N (m+1+j) x) (N-m)]
    have hb : m + 1 + (N - m) = N + 1 := by omega
    rw [hb, Aterm_top_zero N (by omega)]
    simp only [sub_zero]
    unfold Aterm
    rw [show m+1-1 = m from by omega, show N - (m+1) = N - 1 - m from by omega]
  rw [← htel]
  exact hsum

theorem integrand_cont (N m : ℕ) :
    Continuous (fun t : ℝ => (N : ℝ) * (Nat.choose (N-1) m : ℝ) * t ^ m * (1 - t) ^ (N - 1 - m)) := by
  fun_prop

theorem tail_at_zero (N m : ℕ) :
    (∑ k ∈ Finset.Ico (m+1) (N+1), (Nat.choose N k : ℝ) * (0:ℝ) ^ k * (1 - 0) ^ (N - k)) = 0 := by
  apply Finset.sum_eq_zero
  intro k hk
  rw [Finset.mem_Ico] at hk
  have : (0:ℝ) ^ k = 0 := by
    apply zero_pow; omega
  rw [this]; ring

end IncBeta

open IncBeta

theorem solution (N m : ℕ) (h : m < N) (p : ℝ) :
    ∑ k ∈ Finset.Ioo m (N + 1), binomialCardinalityProb N k p
      = ∫ t in (0:ℝ)..p, (N : ℝ) * (Nat.choose (N-1) m : ℝ) * t ^ m * (1 - t) ^ (N - 1 - m) := by
  unfold binomialCardinalityProb
  have hset : Finset.Ioo m (N + 1) = Finset.Ico (m+1) (N+1) := by
    ext x; simp only [Finset.mem_Ioo, Finset.mem_Ico]; omega
  rw [hset]
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun p : ℝ => ∑ k ∈ Finset.Ico (m+1) (N+1),
        (Nat.choose N k : ℝ) * p ^ k * (1 - p) ^ (N - k))
    (f' := fun t : ℝ => (N : ℝ) * (Nat.choose (N-1) m : ℝ) * t ^ m * (1 - t) ^ (N - 1 - m))
    (a := 0) (b := p)
    (fun t _ => tail_deriv N m h t)
    ((integrand_cont N m).intervalIntegrable 0 p)
  rw [hftc, tail_at_zero N m, sub_zero]
