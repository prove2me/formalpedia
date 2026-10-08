-- Prove2me | solution 1 for SuttonBartoRL.Traces.lambda_return_finite_form
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T13:48:56.668726+00:00
-- url     : https://prove2.me/submissions/8c062551-bc68-47f1-b623-92498b516387

import Mathlib
import Definitions.Def_SuttonBartoRL_Traces_LambdaReturn

set_option autoImplicit false

open SuttonBartoRL.Traces in
lemma df55_tail_eq {St : Type} {d : ℕ} (γ : ℝ)
    (vhat : St → EuclideanSpace ℝ (Fin d) → ℝ) (w : EuclideanSpace ℝ (Fin d))
    (e : Episode St) (t : ℕ) (ht : t < e.T) (n : ℕ) (hn : e.T - t - 1 ≤ n) :
    nstepReturn γ vhat w e t (n + 1) = ret γ e t := by
  unfold nstepReturn
  split_ifs with h
  · have hT : t + (n + 1) = e.T := by omega
    rw [hT]
    have hv : value vhat w e e.T = 0 := by simp [value]
    rw [hv, mul_zero, add_zero]
    unfold ret
    rw [Finset.sum_Ico_eq_sum_range]
    have : e.T - t = n + 1 := by omega
    rw [this]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Nat.add_sub_cancel_left]
  · rfl

open SuttonBartoRL.Traces in
theorem solution {St : Type} {d : ℕ} (γ lam : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (hlam0 : 0 ≤ lam) (hlam1 : lam < 1)
    (vhat : St → EuclideanSpace ℝ (Fin d) → ℝ) (w : EuclideanSpace ℝ (Fin d))
    (e : Episode St) (t : ℕ) (ht : t < e.T) :
    Summable (fun n : ℕ => lam ^ n * nstepReturn γ vhat w e t (n + 1)) ∧
      lambdaReturn γ lam vhat w e t =
        (1 - lam) * ∑ n ∈ Finset.range (e.T - t - 1), lam ^ n * nstepReturn γ vhat w e t (n + 1)
          + lam ^ (e.T - t - 1) * ret γ e t := by
  set m := e.T - t - 1 with hm
  set f : ℕ → ℝ := fun n => lam ^ n * nstepReturn γ vhat w e t (n + 1) with hf
  have htail : (fun n => f (n + m)) = fun n => (lam ^ m * ret γ e t) * lam ^ n := by
    funext n
    simp only [hf]
    rw [df55_tail_eq γ vhat w e t ht (n + m) (by omega), pow_add]
    ring
  have hgeo : Summable (fun n : ℕ => (lam ^ m * ret γ e t) * lam ^ n) :=
    (summable_geometric_of_lt_one hlam0 hlam1).mul_left _
  have hs : Summable f := by
    rw [← summable_nat_add_iff m, htail]
    exact hgeo
  refine ⟨hs, ?_⟩
  unfold lambdaReturn
  change (1 - lam) * ∑' n, f n = _
  rw [← hs.sum_add_tsum_nat_add m, htail, tsum_mul_left, tsum_geometric_of_lt_one hlam0 hlam1]
  have h1 : (1 - lam) ≠ 0 := by linarith
  field_simp
