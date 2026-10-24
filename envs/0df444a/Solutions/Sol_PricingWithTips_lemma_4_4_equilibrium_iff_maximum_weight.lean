-- Prove2me | solution 1 for PricingWithTips.lemma_4_4_equilibrium_iff_maximum_weight
-- status  : ACCEPTED   (prove)
-- author  : @qmaai2907271020
-- created : 2026-10-20T22:29:26.607686+00:00
-- url     : https://prove2.me/submissions/9977313f-4b15-452b-b939-b81669b8c0d6

import Theorems.Thm_PricingWithTips_lemma_4_4_only_if
import Theorems.Thm_PricingWithTips_lemma_4_4_if

open PricingWithTips

variable {B S D : Type*} [Fintype B] [Fintype S] [Fintype D]
  [DecidableEq B] [DecidableEq S] [DecidableEq D]

theorem solution [Nonempty D]
    (M : Market B S D) (A : Allocation B S D) (uBar : D → ℝ)
    (hu : IsMaximalCourierUtility M A uBar) :
    HasWithTipEquilibriumAt M A ↔
      IsMaximumWeight A.toBuyerMatching (adjustedValue M A uBar) := by
  constructor
  · exact lemma_4_4_only_if M A uBar hu
  · exact lemma_4_4_if M A uBar hu
