-- Prove2me | solution 1 for SuttonBartoRL.BatchTD.mc_error_eq_sum_q_td_errors
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T08:09:10.092392+00:00
-- url     : https://prove2.me/submissions/c828eece-0f60-47a8-a52c-9569740ef3f8

import Mathlib
import Definitions.Def_SuttonBartoRL_BatchTD_Episodes

set_option autoImplicit false

open SuttonBartoRL.BatchTD in
lemma p380_sum_split (γ : ℝ) (f : ℕ → ℝ) (t L : ℕ) (h : t < L) :
    ∑ k ∈ Finset.Ico t L, γ ^ (k - t) * f k =
      f t + γ * ∑ k ∈ Finset.Ico (t + 1) L, γ ^ (k - (t + 1)) * f k := by
  rw [Finset.sum_eq_sum_Ico_succ_bot h, Finset.mul_sum]
  simp only [Nat.sub_self, pow_zero, one_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_Ico] at hk
  have : k - t = (k - (t + 1)) + 1 := by omega
  rw [this, pow_succ]
  ring

open SuttonBartoRL.BatchTD in
theorem solution {S A : Type} (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (Q : S → A → ℝ) (e : Episode (S × A)) (t : ℕ) (ht : t ≤ e.length) :
    ret γ e t - extQ Q (stateAt e t) =
      ∑ k ∈ Finset.Ico t e.length, γ ^ (k - t) * qTdError γ Q e k := by
  obtain ⟨n, hn⟩ : ∃ n, e.length - t = n := ⟨_, rfl⟩
  induction n generalizing t with
  | zero =>
    have hte : t = e.length := by omega
    subst hte
    have h1 : stateAt e e.length = none := by
      simp [stateAt]
    simp [ret, h1, extQ]
  | succ n ih =>
    have hlt : t < e.length := by omega
    have ih' := ih (t + 1) (by omega) (by omega)
    rw [p380_sum_split γ _ t e.length hlt, ← ih']
    have hret : ret γ e t = nextReward e t + γ * ret γ e (t + 1) := by
      unfold ret
      exact p380_sum_split γ (nextReward e) t e.length hlt
    rw [hret]
    unfold qTdError
    ring
