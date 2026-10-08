-- Prove2me | solution 1 for SuttonBartoRL.Traces.lambda_return_recursion
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T14:11:21.491589+00:00
-- url     : https://prove2.me/submissions/9424e0ab-2322-4d62-8e89-c324f2d0a130

import Mathlib
import Definitions.Def_SuttonBartoRL_Traces_LambdaReturn

set_option autoImplicit false

open SuttonBartoRL.Traces in
theorem lrr488_ret_succ {St : Type} (γ : ℝ) (e : Episode St) (t : ℕ) (ht : t < e.T) :
    ret γ e t = e.R (t + 1) + γ * ret γ e (t + 1) := by
  unfold ret
  rw [Finset.sum_eq_sum_Ico_succ_bot ht, Nat.sub_self, pow_zero, one_mul, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_Ico] at hk
  rw [show k - t = (k - (t + 1)) + 1 by omega, pow_succ]
  ring

open SuttonBartoRL.Traces in
theorem lrr488_nstep_one {St : Type} {d : ℕ} (γ : ℝ)
    (vhat : St → EuclideanSpace ℝ (Fin d) → ℝ) (w : EuclideanSpace ℝ (Fin d))
    (e : Episode St) (t : ℕ) (ht : t < e.T) :
    nstepReturn γ vhat w e t 1 = e.R (t + 1) + γ * value vhat w e (t + 1) := by
  unfold nstepReturn
  rw [if_pos (by omega)]
  simp

open SuttonBartoRL.Traces in
theorem lrr488_nstep_succ {St : Type} {d : ℕ} (γ : ℝ)
    (vhat : St → EuclideanSpace ℝ (Fin d) → ℝ) (w : EuclideanSpace ℝ (Fin d))
    (e : Episode St) (t : ℕ) (ht : t < e.T) (n : ℕ) :
    nstepReturn γ vhat w e t (n + 2) =
      e.R (t + 1) + γ * nstepReturn γ vhat w e (t + 1) (n + 1) := by
  unfold nstepReturn
  by_cases h : t + (n + 2) ≤ e.T
  · rw [if_pos h, if_pos (by omega), Finset.sum_range_succ' _ (n + 1)]
    have hs : ∑ i ∈ Finset.range (n + 1), γ ^ (i + 1) * e.R (t + (i + 1) + 1) =
        γ * ∑ i ∈ Finset.range (n + 1), γ ^ i * e.R (t + 1 + i + 1) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [show t + (i + 1) + 1 = t + 1 + i + 1 by omega]
      ring
    rw [hs, show t + 1 + (n + 1) = t + (n + 2) by omega]
    simp only [pow_zero, one_mul, add_zero]
    ring
  · rw [if_neg h, if_neg (by omega)]
    exact lrr488_ret_succ γ e t ht

open SuttonBartoRL.Traces in
theorem lrr488_summable {St : Type} {d : ℕ} (γ lam : ℝ) (hlam0 : 0 ≤ lam) (hlam1 : lam < 1)
    (vhat : St → EuclideanSpace ℝ (Fin d) → ℝ) (w : EuclideanSpace ℝ (Fin d))
    (e : Episode St) (s : ℕ) :
    Summable (fun n : ℕ => lam ^ n * nstepReturn γ vhat w e s (n + 1)) := by
  have hg : Summable (fun n : ℕ => lam ^ n * ret γ e s) :=
    (summable_geometric_of_lt_one hlam0 hlam1).mul_right _
  have hd : Summable (fun n : ℕ =>
      lam ^ n * nstepReturn γ vhat w e s (n + 1) - lam ^ n * ret γ e s) := by
    apply summable_of_ne_finset_zero (s := Finset.range e.T)
    intro n hn
    rw [Finset.mem_range] at hn
    unfold nstepReturn
    rw [if_neg (by omega)]
    ring
  convert hd.add hg using 1
  ext n
  ring

open SuttonBartoRL.Traces in
theorem solution {St : Type} {d : ℕ} (γ lam : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (hlam0 : 0 ≤ lam) (hlam1 : lam < 1)
    (vhat : St → EuclideanSpace ℝ (Fin d) → ℝ) (w : EuclideanSpace ℝ (Fin d))
    (e : Episode St) (t : ℕ) (ht : t < e.T) :
    lambdaReturn γ lam vhat w e t =
      e.R (t + 1) + γ * ((1 - lam) * value vhat w e (t + 1)
        + lam * lambdaReturn γ lam vhat w e (t + 1)) := by
  unfold lambdaReturn
  have hS := lrr488_summable γ lam hlam0 hlam1 vhat w e t
  have hS1 := lrr488_summable γ lam hlam0 hlam1 vhat w e (t + 1)
  have hG : Summable (fun n : ℕ => lam ^ n) := summable_geometric_of_lt_one hlam0 hlam1
  rw [hS.tsum_eq_zero_add]
  have h2 : ∀ n : ℕ, lam ^ (n + 1) * nstepReturn γ vhat w e t (n + 1 + 1) =
      lam * e.R (t + 1) * lam ^ n +
        (lam * γ) * (lam ^ n * nstepReturn γ vhat w e (t + 1) (n + 1)) := by
    intro n
    rw [show n + 1 + 1 = n + 2 by omega, lrr488_nstep_succ γ vhat w e t ht n]
    ring
  simp_rw [h2]
  rw [(hG.mul_left _).tsum_add (hS1.mul_left _), tsum_mul_left, tsum_mul_left,
    tsum_geometric_of_lt_one hlam0 hlam1]
  simp only [pow_zero, one_mul, zero_add]
  rw [lrr488_nstep_one γ vhat w e t ht]
  have hne : (1 - lam) ≠ 0 := by linarith
  field_simp
  ring
