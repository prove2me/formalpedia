-- Prove2me | solution 1 for SuttonBartoRL.ImportanceSampling.trajectory_probability_ratio
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T11:00:17.098514+00:00
-- url     : https://prove2.me/submissions/ea82f19f-c84f-4491-a9a9-4ce3148323e6

import Mathlib
import Definitions.Def_SuttonBartoRL_ImportanceSampling_Episodes

open SuttonBartoRL.ImportanceSampling in
theorem solution {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]
    (M : MDP S A) (term : Finset S) (π b : SuttonBartoRL.FiniteMDP.Policy S A) (s : S) (n : ℕ)
    (st : Fin (n + 1) → S) (ac : Fin n → A) :
    (∀ μ : SuttonBartoRL.FiniteMDP.Policy S A,
      ∑ rw : Fin n → M.R, episodeProb M term μ s ((st, ac, rw) : Episode M n) =
        trajectoryProb M term μ s st ac) ∧
    (trajectoryProb M term b s st ac ≠ 0 → ∀ rw : Fin n → M.R,
      trajectoryProb M term π s st ac / trajectoryProb M term b s st ac =
        Episode.isRatio π b ((st, ac, rw) : Episode M n) n) := by
  refine ⟨fun μ => ?_, fun hb rw => ?_⟩
  · have e1 : ∀ x : Fin n → M.R, episodeProb M term μ s ((st, ac, x) : Episode M n) =
        if st 0 = s ∧ (∀ k : Fin n, st k.castSucc ∉ term) ∧ st (Fin.last n) ∈ term then
          ∏ k : Fin n, μ.prob (st k.castSucc) (ac k) *
            M.p (st k.castSucc) (ac k) (st k.succ) (x k : ℝ)
        else 0 := fun x => rfl
    simp_rw [e1]
    unfold trajectoryProb
    by_cases h : st 0 = s ∧ (∀ k : Fin n, st k.castSucc ∉ term) ∧ st (Fin.last n) ∈ term
    · simp only [if_pos h]
      have key : ∀ k : Fin n, μ.prob (st k.castSucc) (ac k) * M.trans (st k.castSucc) (ac k) (st k.succ)
          = ∑ r : M.R, μ.prob (st k.castSucc) (ac k) * M.p (st k.castSucc) (ac k) (st k.succ) (r : ℝ) := by
        intro k
        rw [MDP.trans, Finset.mul_sum, Finset.sum_coe_sort M.R
          (fun r => μ.prob (st k.castSucc) (ac k) * M.p (st k.castSucc) (ac k) (st k.succ) r)]
      simp_rw [key]
      rw [Fintype.prod_sum]
    · simp only [if_neg h, Finset.sum_const_zero]
  · unfold trajectoryProb at hb ⊢
    have h : st 0 = s ∧ (∀ k : Fin n, st k.castSucc ∉ term) ∧ st (Fin.last n) ∈ term := by
      by_contra h
      exact hb (if_neg h)
    rw [if_pos h] at hb
    rw [if_pos h, if_pos h, ← Finset.prod_div_distrib]
    unfold Episode.isRatio
    simp only [Episode.states, Episode.actions]
    rw [Finset.filter_true_of_mem (fun k _ => k.isLt)]
    apply Finset.prod_congr rfl
    intro k _
    have hk := (Finset.prod_ne_zero_iff.mp hb) k (Finset.mem_univ _)
    have hT : M.trans (st k.castSucc) (ac k) (st k.succ) ≠ 0 := right_ne_zero_of_mul hk
    exact mul_div_mul_right _ _ hT
