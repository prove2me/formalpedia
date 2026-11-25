-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.I.evl_alg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:43:58.782644+00:00
-- url     : https://prove2.me/submissions/4b551dfd-b10f-45a3-89d8-4b3b4153c7bf

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_BergmanExistsStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_EvLeviA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.I
open scoped ComplexConjugate ContDiff
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.I
theorem _root_.solution (c ee S Q p1 p2 b1 b2 l : ℝ) (hc : 0 < c) (hee : 0 < ee) (hS : 0 ≤ S)
    (hQ : 0 ≤ Q) (hCS : p1 ^ 2 + p2 ^ 2 ≤ S * Q) :
    c ^ 2 * ee ^ 2 * ((p1 - S * b1) ^ 2 + (p2 - S * b2) ^ 2) ≤
        c * (S * ee) * (c * (Q * ee + S * (ee * (b1 ^ 2 + b2 ^ 2 - l)) -
          2 * ee * (p1 * b1 + p2 * b2)) + c * (S * ee) * l) ∧
      0 ≤ c * (Q * ee + S * (ee * (b1 ^ 2 + b2 ^ 2 - l)) - 2 * ee * (p1 * b1 + p2 * b2)) +
        c * (S * ee) * l := by
  constructor
  · have h : c * (S * ee) * (c * (Q * ee + S * (ee * (b1 ^ 2 + b2 ^ 2 - l)) -
          2 * ee * (p1 * b1 + p2 * b2)) + c * (S * ee) * l) -
        c ^ 2 * ee ^ 2 * ((p1 - S * b1) ^ 2 + (p2 - S * b2) ^ 2) =
        (c * ee) ^ 2 * (S * Q - (p1 ^ 2 + p2 ^ 2)) := by ring
    have : 0 ≤ (c * ee) ^ 2 * (S * Q - (p1 ^ 2 + p2 ^ 2)) :=
      mul_nonneg (sq_nonneg _) (sub_nonneg.2 hCS)
    linarith
  · have hX : 0 ≤ Q + S * (b1 ^ 2 + b2 ^ 2) - 2 * (p1 * b1 + p2 * b2) := by
      rcases hS.eq_or_lt with h0 | hpos
      · subst h0
        have h1 : p1 = 0 := by nlinarith [sq_nonneg p1, sq_nonneg p2]
        have h2 : p2 = 0 := by nlinarith [sq_nonneg p1, sq_nonneg p2]
        subst h1; subst h2; nlinarith
      · have hm : S * (Q + S * (b1 ^ 2 + b2 ^ 2) - 2 * (p1 * b1 + p2 * b2)) =
            (S * Q - (p1 ^ 2 + p2 ^ 2)) + ((p1 - S * b1) ^ 2 + (p2 - S * b2) ^ 2) := by ring
        have h3 : 0 ≤ S * (Q + S * (b1 ^ 2 + b2 ^ 2) - 2 * (p1 * b1 + p2 * b2)) := by
          rw [hm]; nlinarith [sq_nonneg (p1 - S * b1), sq_nonneg (p2 - S * b2)]
        exact nonneg_of_mul_nonneg_right (by linarith [h3, mul_comm S (Q + S * (b1 ^ 2 + b2 ^ 2) - 2 * (p1 * b1 + p2 * b2))]) hpos
    have h : c * (Q * ee + S * (ee * (b1 ^ 2 + b2 ^ 2 - l)) - 2 * ee * (p1 * b1 + p2 * b2)) +
        c * (S * ee) * l = (c * ee) * (Q + S * (b1 ^ 2 + b2 ^ 2) - 2 * (p1 * b1 + p2 * b2)) := by
      ring
    rw [h]; exact mul_nonneg (by positivity) hX
end ReciprocityTheory.L2DbarEstimates.I
