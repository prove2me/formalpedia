-- Prove2me | solution 1 for PosteriorSamplingRL.Regret.lemma2_dynamic_programming
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T10:09:29.364998+00:00
-- url     : https://prove2.me/submissions/441d2f4e-df5b-4f78-9b58-b1f865e3c8d9

import Mathlib
import Definitions.Def_PosteriorSamplingRL_Regret_MDP
set_option autoImplicit false
open PosteriorSamplingRL.Regret

lemma psr_occ_shift {S A τ : ℕ} {Θ : Type} [MeasurableSpace Θ] (F : MDPFamily S A Θ) (θ : Θ)
    (π : Policy S A τ) (i : ℕ) (n : ℕ) :
    ∀ (s s'' : Fin S), occ F θ π i s (n + 1) s'' =
      ∑ s', stepKernel F θ π i s s' * occ F θ π (i + 1) s' n s'' := by
  induction n with
  | zero =>
    intro s s''
    simp [occ]
  | succ n ih =>
    intro s s''
    rw [occ]
    simp_rw [ih]
    simp only [occ]
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun s' _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    have : i + (n + 1) = i + 1 + n := by omega
    rw [this]
    ring

theorem solution (S A τ : ℕ) (Θ : Type) [MeasurableSpace Θ]
    (F : MDPFamily S A Θ) (θ : Θ) (π : Policy S A τ) :
    (∀ (j : ℕ) (hj : j < τ) (s : Fin S),
      value F θ π j s = bellman F θ (fun s' => π s' ⟨j, hj⟩) (value F θ π (j + 1)) s) ∧
    value F θ π τ = 0 := by
  refine ⟨?_, ?_⟩
  · intro j hj s
    unfold value bellman
    rw [Finset.sum_eq_sum_Ico_succ_bot hj]
    have h0 : ∑ s', stepDist F θ π j s j s' * rewardAt F θ π j s' = meanReward F θ s (π s ⟨j, hj⟩) := by
      simp [stepDist, occ, rewardAt, hj]
    rw [h0]
    congr 1
    have key : ∀ j' ∈ Finset.Ico (j + 1) τ, ∀ s' : Fin S, stepDist F θ π j s j' s' =
        ∑ s1, F.P θ s (π s ⟨j, hj⟩) s1 * stepDist F θ π (j + 1) s1 j' s' := by
      intro j' hj' s'
      rw [Finset.mem_Ico] at hj'
      have e : j' - j = (j' - (j + 1)) + 1 := by omega
      simp only [stepDist]
      rw [e, psr_occ_shift]
      refine Finset.sum_congr rfl (fun s1 _ => ?_)
      simp [stepKernel, hj]
    rw [Finset.sum_congr rfl (fun j' hj' => Finset.sum_congr rfl (fun s' _ => by rw [key j' hj' s']))]
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_congr rfl (fun j' _ => Finset.sum_comm)]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j' _ => Finset.sum_congr rfl (fun s' _ => ?_)))
    ring
  · funext s
    simp [value]
