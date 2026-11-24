-- Prove2me | solution 1 for TaoFivePrimes.theorem51_vaughan_split_repaired
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-23T05:32:13.453674+00:00
-- url     : https://prove2.me/submissions/6858c1b4-9d93-4e44-868d-4042aae783ce

import Theorems.Thm_TaoFivePrimes_smoothedExpSum_eq_eta0VaughanTypeISum_add_centredPairSum
import Theorems.Thm_TaoFivePrimes_theorem51_child3_restricted_log_repair

open TaoFivePrimes

theorem solution
    (x alpha U V : ℝ) (hU : 40 ≤ U) (hV : 40 ≤ V)
    (hUx : U < x) (hVx : V < x)
    (hUVx : U * V ≤ x / 4) (hUV2 : x ≤ U * V ^ 2) :
    ∃ c : ℕ → ℂ, (∀ d ∈ TaoFivePrimes.theorem51Divisors U V, ‖c d‖ ≤ 1) ∧
      ‖TaoFivePrimes.smoothedExpSum TaoFivePrimes.eta0 2 x alpha‖ ≤
        (∑ d ∈ TaoFivePrimes.theorem51Divisors U V, ‖
          (if d ≤ ⌊U⌋₊
            then ∑ w ∈ TaoFivePrimes.TypeIOuterDAssembly.fullInnerSupport x d,
                   ((Real.log (w : ℝ) : ℂ) * TaoFivePrimes.eta0VaughanTest x alpha (d * w))
            else ∑ w ∈ TaoFivePrimes.TypeIOuterDAssembly.transferredInnerSupport x V d,
                   ((Real.log (w : ℝ) : ℂ) * TaoFivePrimes.eta0VaughanTest x alpha (d * w)))
          + c d * (Real.log d : ℂ) *
              (∑ w ∈ TaoFivePrimes.TypeIOuterDAssembly.fullInnerSupport x d,
                TaoFivePrimes.eta0VaughanTest x alpha (d * w))‖)
        + TaoFivePrimes.theorem51TypeII x alpha U V := by
  have h1 :=
    TaoFivePrimes.smoothedExpSum_eq_eta0VaughanTypeISum_add_centredPairSum
      x alpha U V hU hV hUx hVx hUVx hUV2
  obtain ⟨c, hc, hEV⟩ :=
    TaoFivePrimes.theorem51_child3_restricted_log_repair
      x alpha U V hU hV hUx hVx hUVx hUV2
  refine ⟨c, hc, ?_⟩
  rw [h1, TaoFivePrimes.theorem51TypeII]
  exact le_trans (norm_add_le _ _) (add_le_add_left hEV _)
