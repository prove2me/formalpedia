-- Prove2me | solution 1 for Waiting.waiting_time_density
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-06-21T17:57:48.470427+00:00
-- url     : https://prove2.me/submissions/e2754e50-35eb-4ef1-8522-f6c1cd75c991

import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Algebra.BigOperators.Intervals

set_option autoImplicit false

open scoped BigOperators
open Finset


/-- One binomial-tail term, as a function of `p`. -/
noncomputable def wt_binTerm (N k : ℕ) (p : ℝ) : ℝ :=
  (Nat.choose N k : ℝ) * p ^ k * (1 - p) ^ (N - k)

/-- `wt_Aterm k(x) = N·C(N-1,k-1)·x^{k-1}·(1-x)^{N-k}` (Siegel §2.1.1 telescoping term). -/
noncomputable def wt_Aterm (N k : ℕ) (x : ℝ) : ℝ :=
  (N : ℝ) * (Nat.choose (N-1) (k-1) : ℝ) * x ^ (k-1) * (1 - x) ^ (N - k)
noncomputable def wt_Bterm (N k : ℕ) (x : ℝ) : ℝ :=
  (N : ℝ) * (Nat.choose (N-1) k : ℝ) * x ^ k * (1 - x) ^ (N - 1 - k)

theorem wt_term_deriv (N k : ℕ) (hk1 : 1 ≤ k) (hkN : k ≤ N) (x : ℝ) :
    HasDerivAt (fun p : ℝ => (Nat.choose N k : ℝ) * p ^ k * (1 - p) ^ (N - k))
      (wt_Aterm N k x - wt_Bterm N k x) x := by
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
  simp only [wt_Aterm, wt_Bterm, he]
  rw [e1, e2]
  ring

theorem wt_Bterm_eq_Aterm_succ (N k : ℕ) (x : ℝ) : wt_Bterm N k x = wt_Aterm N (k+1) x := by
  unfold wt_Aterm wt_Bterm
  have h1 : k + 1 - 1 = k := by omega
  rw [h1]; congr 2; omega

theorem wt_Aterm_top_zero (N : ℕ) (hN : 1 ≤ N) (x : ℝ) : wt_Aterm N (N+1) x = 0 := by
  unfold wt_Aterm
  have hz : Nat.choose (N-1) (N+1-1) = 0 := by
    apply Nat.choose_eq_zero_of_lt; omega
  rw [hz]; simp

/-- Derivative of the binomial UPPER tail in `p`: telescopes to a single term. -/
theorem wt_tail_deriv (N m : ℕ) (h : m < N) (x : ℝ) :
    HasDerivAt (fun p : ℝ => ∑ k ∈ Finset.Ico (m+1) (N+1),
        (Nat.choose N k : ℝ) * p ^ k * (1 - p) ^ (N - k))
      ((N : ℝ) * (Nat.choose (N-1) m : ℝ) * x ^ m * (1 - x) ^ (N - 1 - m)) x := by
  have hsum : HasDerivAt (fun p : ℝ => ∑ k ∈ Finset.Ico (m+1) (N+1),
        (Nat.choose N k : ℝ) * p ^ k * (1 - p) ^ (N - k))
      (∑ k ∈ Finset.Ico (m+1) (N+1), (wt_Aterm N k x - wt_Bterm N k x)) x := by
    have hh := HasDerivAt.sum (u := Finset.Ico (m+1) (N+1))
      (A := fun k => fun p : ℝ => (Nat.choose N k : ℝ) * p ^ k * (1 - p) ^ (N - k))
      (A' := fun k => wt_Aterm N k x - wt_Bterm N k x) (x := x)
      (fun k hk => by rw [Finset.mem_Ico] at hk; exact wt_term_deriv N k (by omega) (by omega) x)
    have hfe : (fun p : ℝ => ∑ k ∈ Finset.Ico (m+1) (N+1),
        (Nat.choose N k : ℝ) * p ^ k * (1 - p) ^ (N - k))
        = (∑ k ∈ Finset.Ico (m+1) (N+1), fun p : ℝ =>
            (Nat.choose N k : ℝ) * p ^ k * (1 - p) ^ (N - k)) := by
      funext p; simp only [Finset.sum_apply]
    rw [hfe]; exact hh
  have htel : (∑ k ∈ Finset.Ico (m+1) (N+1), (wt_Aterm N k x - wt_Bterm N k x))
      = (N : ℝ) * (Nat.choose (N-1) m : ℝ) * x ^ m * (1 - x) ^ (N - 1 - m) := by
    have hstep : (∑ k ∈ Finset.Ico (m+1) (N+1), (wt_Aterm N k x - wt_Bterm N k x))
        = ∑ k ∈ Finset.Ico (m+1) (N+1), (wt_Aterm N k x - wt_Aterm N (k+1) x) := by
      apply Finset.sum_congr rfl; intro k _; rw [wt_Bterm_eq_Aterm_succ]
    rw [hstep, Finset.sum_Ico_eq_sum_range]
    have hlen : N + 1 - (m + 1) = N - m := by omega
    rw [hlen]
    have hcongr : (∑ i ∈ Finset.range (N-m), (wt_Aterm N (m+1+i) x - wt_Aterm N (m+1+i+1) x))
        = ∑ i ∈ Finset.range (N-m), ((fun j => wt_Aterm N (m+1+j) x) i - (fun j => wt_Aterm N (m+1+j) x) (i+1)) := by
      apply Finset.sum_congr rfl; intro i _; rfl
    rw [hcongr, Finset.sum_range_sub' (fun j => wt_Aterm N (m+1+j) x) (N-m)]
    have hb : m + 1 + (N - m) = N + 1 := by omega
    rw [hb, wt_Aterm_top_zero N (by omega)]
    simp only [sub_zero]
    unfold wt_Aterm
    rw [show m+1-1 = m from by omega, show N - (m+1) = N - 1 - m from by omega]
  rw [← htel]; exact hsum

theorem solution (N m : ℕ) (lam : ℝ) (h : m < N) (t : ℝ) :
    HasDerivAt
      (fun s : ℝ => ∑ k ∈ Finset.Ico (m+1) (N+1),
        (Nat.choose N k : ℝ) * (1 - Real.exp (-(lam * s))) ^ k
          * (Real.exp (-(lam * s))) ^ (N - k))
      ((N : ℝ) * (Nat.choose (N-1) m : ℝ) * (1 - Real.exp (-(lam * t))) ^ m
          * (Real.exp (-(lam * t))) ^ (N - m) * lam) t := by
  -- inner substitution q(s) = 1 - exp(-(lam*s)),  q'(t) = lam * exp(-(lam*t))
  have hexp : HasDerivAt (fun s : ℝ => Real.exp (-(lam * s)))
      (Real.exp (-(lam * t)) * (-lam)) t := by
    have hinner : HasDerivAt (fun s : ℝ => -(lam * s)) (-lam) t := by
      have : HasDerivAt (fun s : ℝ => lam * s) lam t := by
        simpa using (hasDerivAt_id t).const_mul lam
      exact this.fun_neg
    exact (Real.hasDerivAt_exp (-(lam * t))).comp t hinner
  have hq : HasDerivAt (fun s : ℝ => 1 - Real.exp (-(lam * s)))
      (lam * Real.exp (-(lam * t))) t := by
    have := hexp.const_sub 1
    exact this.congr_deriv (by ring)
  -- outer: the binomial upper tail at q
  set q := 1 - Real.exp (-(lam * t)) with hqdef
  have houter := wt_tail_deriv N m h q
  -- chain rule: derivative of  (TailSum ∘ q)  is  TailDeriv(q) * q'(t)
  have hcomp := houter.comp t hq
  -- hcomp : HasDerivAt (TailSum ∘ q(·)) (TailDeriv(q) * (lam * exp(-lam t))) t
  -- rewrite the inner-composition function and the value
  have hfun : (fun s : ℝ => ∑ k ∈ Finset.Ico (m+1) (N+1),
        (Nat.choose N k : ℝ) * (1 - Real.exp (-(lam * s))) ^ k
          * (Real.exp (-(lam * s))) ^ (N - k))
      = (fun p : ℝ => ∑ k ∈ Finset.Ico (m+1) (N+1),
          (Nat.choose N k : ℝ) * p ^ k * (1 - p) ^ (N - k)) ∘ (fun s : ℝ => 1 - Real.exp (-(lam * s))) := by
    funext s
    simp only [Function.comp_apply]
    apply Finset.sum_congr rfl
    intro k _
    have : (1 - (1 - Real.exp (-(lam * s)))) = Real.exp (-(lam * s)) := by ring
    rw [this]
  rw [hfun]
  refine hcomp.congr_deriv ?_
  -- value:  N·C(N-1,m)·q^m·(exp)^{N-m}·lam  =  (N·C(N-1,m)·q^m·(1-q)^{N-1-m}) · (lam·exp)
  have h1q : (1 - q) = Real.exp (-(lam * t)) := by rw [hqdef]; ring
  rw [h1q]
  have hNm : N - m = (N - 1 - m) + 1 := by omega
  rw [hNm, pow_succ]
  ring
