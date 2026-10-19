-- Prove2me | solution 1 for TokenFinance.MoralHazard.lemma_5
-- status  : ACCEPTED   (prove)
-- author  : @mihalyimark
-- created : 2026-10-19T11:08:20.662267+00:00
-- url     : https://prove2.me/submissions/65856c3e-ae90-496c-b901-6b36eef463e1

-- DS19C standalone solution for TokenFinance.MoralHazard.lemma_5
-- (theorem_id f342a7d7-4b21-4057-b071-7417ca156ae7), Lemma 5, p. 32, (30).
--
-- Recovered from the partial MiMo6 file
-- Solutions/Sol_MIMO6_TokenFinance_MoralHazard_lemma_5.lean (attribution: MiMo6;
-- inspected, recompiled and statement-checked by DS19C). The mathematical argument is:
-- clear the positive denominator (1−τ)³; the claim becomes (λ(1−τ))³ > (λ−τ)³.
-- At the first power λ(1−τ) − (λ−τ) = τ(1−λ) > 0, and both bases are positive, so
-- the difference of cubes factors as (positive) × (sum of positive squares).
import Mathlib

theorem solution (τ lam : ℝ) (hτ : 0 < τ) (hτl : τ < lam) (hl1 : lam < 1) :
    lam ^ 3 > (lam - τ) ^ 3 / (1 - τ) ^ 3 := by
  have hpos : 0 < 1 - τ := sub_pos_of_lt (lt_trans hτl hl1)
  have hb0 : 0 < lam - τ := sub_pos_of_lt hτl
  have hlin : lam * (1 - τ) - (lam - τ) = τ * (1 - lam) := by ring
  have hlin' : lam - τ < lam * (1 - τ) := by nlinarith [hlin, hτ, hl1]
  have ha0 : 0 < lam * (1 - τ) := lt_trans hb0 hlin'
  have hcub : (lam * (1 - τ)) ^ 3 > (lam - τ) ^ 3 := by
    have hfac : (lam * (1 - τ)) ^ 3 - (lam - τ) ^ 3 =
        ((lam * (1 - τ)) - (lam - τ)) *
          ((lam * (1 - τ)) ^ 2 + (lam * (1 - τ)) * (lam - τ) + (lam - τ) ^ 2) := by ring
    have hsq : 0 < (lam * (1 - τ)) ^ 2 + (lam * (1 - τ)) * (lam - τ) + (lam - τ) ^ 2 := by
      positivity
    nlinarith [hfac, hsq, hlin']
  rw [gt_iff_lt, div_lt_iff₀ (pow_pos hpos 3)]
  have hmul : (lam * (1 - τ)) ^ 3 = lam ^ 3 * (1 - τ) ^ 3 := by ring
  nlinarith [hmul, hcub]
