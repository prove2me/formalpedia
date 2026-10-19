-- Prove2me | solution 1 for TokenFinance.MoralHazard.lemma_4
-- status  : ACCEPTED   (prove)
-- author  : @mihalyimark
-- created : 2026-10-19T11:08:05.627133+00:00
-- url     : https://prove2.me/submissions/06b666ac-8e27-4363-abc4-c82860429571

-- DS19C standalone solution for TokenFinance.MoralHazard.lemma_4
-- (theorem_id 58bce143-32e5-4bdc-aafe-61e502912ee1), Lemma 4, p. 30, (25).
--
-- Recovered from the partial MiMo6 file
-- Solutions/Sol_MIMO6_TokenFinance_MoralHazard_lemma_4.lean (attribution: MiMo6;
-- inspected, recompiled and statement-checked by DS19C). The mathematical argument is:
-- with 0 < δ < λ < 1 all denominators are positive, so after clearing them the claim is
--   λ³(1−δ)²(1+2δ) − (λ−δ)²(λ+2δ) = δ²·[3λ(1−λ²) + 2δ(λ³−1)] > 0.
-- Since λ³−1 < 0 and δ < λ, we have 2δ(λ³−1) > 2λ(λ³−1), hence the bracket exceeds
--   3λ(1−λ²) + 2λ(λ³−1) = λ(1−λ)²(1+2λ) > 0.
import Mathlib

theorem solution (δ lam : ℝ) (hδ : 0 < δ) (hδl : δ < lam) (hl1 : lam < 1) :
    lam ^ 3 > (lam - δ) ^ 2 / (1 - δ) ^ 2 * ((lam + 2 * δ) / (1 + 2 * δ)) := by
  have h0lam : 0 < lam := lt_trans hδ hδl
  have hd1 : δ < 1 := lt_trans hδl hl1
  have hden1 : 0 < 1 - δ := sub_pos_of_lt hd1
  have hden2 : 0 < 1 + 2 * δ := by linarith
  have h1m : 0 < 1 - lam := sub_pos_of_lt hl1
  have hfac : lam ^ 3 * (1 - δ) ^ 2 * (1 + 2 * δ) - (lam - δ) ^ 2 * (lam + 2 * δ)
      = δ ^ 2 * (3 * lam * (1 - lam ^ 2) + 2 * δ * (lam ^ 3 - 1)) := by ring
  have hneg : lam ^ 3 - 1 < 0 := by nlinarith [hl1, h0lam]
  have hstep : 2 * δ * (lam ^ 3 - 1) > 2 * lam * (lam ^ 3 - 1) := by nlinarith [hδl, hneg]
  have hcomb : 3 * lam * (1 - lam ^ 2) + 2 * lam * (lam ^ 3 - 1)
      = lam * (1 - lam) ^ 2 * (1 + 2 * lam) := by ring
  have hpsq : 0 < (1 - lam) ^ 2 := sq_pos_of_pos h1m
  have h2p : 0 < 1 + 2 * lam := by linarith
  have hpos : 0 < lam * (1 - lam) ^ 2 * (1 + 2 * lam) :=
    mul_pos (mul_pos h0lam hpsq) h2p
  have hbr : 0 < 3 * lam * (1 - lam ^ 2) + 2 * δ * (lam ^ 3 - 1) := by
    nlinarith [hstep, hcomb, hpos]
  have hsq : 0 < δ ^ 2 := sq_pos_of_pos hδ
  have key : (lam - δ) ^ 2 * (lam + 2 * δ) < lam ^ 3 * (1 - δ) ^ 2 * (1 + 2 * δ) := by
    nlinarith [hfac, hsq, hbr]
  have hg : (lam - δ) ^ 2 / (1 - δ) ^ 2 * ((lam + 2 * δ) / (1 + 2 * δ))
      = (lam - δ) ^ 2 * (lam + 2 * δ) / ((1 - δ) ^ 2 * (1 + 2 * δ)) := by
    field_simp [hden1.ne', hden2.ne']
  have hden : 0 < (1 - δ) ^ 2 * (1 + 2 * δ) := mul_pos (pow_pos hden1 2) hden2
  rw [hg]
  rw [gt_iff_lt, div_lt_iff₀ hden]
  linarith [key]
