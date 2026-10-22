-- Prove2me | solution 1 for SuttonBartoRL.ImportanceSampling.ordinary_importance_sampling_unbiased
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T11:02:40.120042+00:00
-- url     : https://prove2.me/submissions/a30f0a6c-412a-4912-afba-cfe4a3052766

import Mathlib
import Definitions.Def_SuttonBartoRL_ImportanceSampling_Episodes

set_option autoImplicit false
open SuttonBartoRL.ImportanceSampling

theorem solution {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]
    (M : MDP S A) (term : Finset S) (π b : SuttonBartoRL.FiniteMDP.Policy S A) (hcov : Coverage π b)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) (s : S) (H : ℕ)
    (hH : ∑ n ∈ Finset.range (H + 1), ∑ e : Episode M n, episodeProb M term b s e = 1) :
    expectation M term b s (fun n e => e.isRatio π b n * e.ret γ) = value M term π γ s := by
  unfold value expectation
  refine tsum_congr fun n => Finset.sum_congr rfl fun e _ => ?_
  have key : episodeProb M term b s e * e.isRatio π b n = episodeProb M term π s e := by
    unfold episodeProb Episode.isRatio
    split_ifs with hc
    · rw [Finset.filter_true_of_mem (fun k _ => k.isLt), ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      by_cases hb : b.prob (e.states k.castSucc) (e.actions k) = 0
      · have hπ : π.prob (e.states k.castSucc) (e.actions k) = 0 := by
          by_contra h
          have := hcov _ _ (lt_of_le_of_ne (π.nonneg _ _) (Ne.symm h))
          rw [hb] at this
          exact lt_irrefl _ this
        simp [hb, hπ]
      · field_simp
    · simp
  calc episodeProb M term b s e * (e.isRatio π b n * e.ret γ)
      = (episodeProb M term b s e * e.isRatio π b n) * e.ret γ := by ring
    _ = episodeProb M term π s e * e.ret γ := by rw [key]
