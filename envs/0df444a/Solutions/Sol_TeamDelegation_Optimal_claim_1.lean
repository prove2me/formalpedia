-- Prove2me | solution 1 for TeamDelegation.Optimal.claim_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T13:40:56.327659+00:00
-- url     : https://prove2.me/submissions/fb49c315-85e6-45f2-8de2-084da99eb27b

import Mathlib
import Definitions.Def_TeamDelegation_Optimal_Model

open TeamDelegation.Optimal

theorem solution (P : Params) (hS : P.Standing)
    (hA1 : P.Assumption1) (W Δsum : ℝ) (hsum : 0 ≤ Δsum)
    (h60 : (P.p2 - P.p0) * W ≥ 2 * P.e)
    (h64 : (P.p2 - P.q2) * W ≥ Δsum)
    (h66 : (P.p2 - P.q0) * W ≥ 2 * P.e + Δsum) :
    SurplusConstraints P W Δsum := by
  obtain ⟨he, hδ0, hδ1, hr0, hr1, hq0, hp2⟩ := hS
  obtain ⟨h01, h12, hq01, hq12, hqp0, hqp1, hqp2, hc1, hc2, hc3, hc4⟩ := hA1
  have hW : 0 < W := by
    by_contra h
    push_neg at h
    have : (P.p2 - P.p0) * W ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith) h
    linarith
  have k59 : 2 * ((P.p2 - P.p1) * W) ≥ (P.p2 - P.p0) * W := by
    have : (P.p2 - P.p0) * W ≤ (2 * (P.p2 - P.p1)) * W :=
      mul_le_mul_of_nonneg_right (by linarith) hW.le
    linarith
  have k65 : 2 * ((P.p2 - P.q1) * W) ≥ (P.p2 - P.q0) * W + (P.p2 - P.q2) * W := by
    have : ((P.p2 - P.q0) + (P.p2 - P.q2)) * W ≤ (2 * (P.p2 - P.q1)) * W :=
      mul_le_mul_of_nonneg_right (by linarith) hW.le
    linarith
  refine ⟨?_, h60, ?_, ?_, ?_, h64, ?_, h66⟩ <;> linarith
