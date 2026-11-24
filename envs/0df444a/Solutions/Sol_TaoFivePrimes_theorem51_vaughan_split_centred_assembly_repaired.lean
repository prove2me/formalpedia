-- Prove2me | solution 1 for TaoFivePrimes.theorem51_vaughan_split_centred_assembly_repaired
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-23T05:36:46.239248+00:00
-- url     : https://prove2.me/submissions/b46b2b29-8083-4589-b938-88919962fa9f

import Theorems.Thm_TaoFivePrimes_smoothedExpSum_eq_eta0VaughanTypeISum_add_centredPairSum
import Theorems.Thm_TaoFivePrimes_theorem51_child3_restricted_log_repair

open TaoFivePrimes

theorem solution
    (x alpha U V : ℝ) (hU : 40 ≤ U) (hV : 40 ≤ V)
    (hUx : U < x) (hVx : V < x)
    (hUVx : U * V ≤ x / 4) (hUV2 : x ≤ U * V ^ 2) :
    (TaoFivePrimes.smoothedExpSum TaoFivePrimes.eta0 2 x alpha =
      TaoFivePrimes.eta0VaughanTypeISum x alpha U V +
      ∑' d : ℕ, ∑' w : ℕ,
        (if U < (d : ℝ) ∧ V < (w : ℝ) ∧ d.Coprime 2 ∧ w.Coprime 2 then
          (ArithmeticFunction.moebius d : ℂ) * (TaoFivePrimes.theorem51Centered V w : ℂ) *
            TaoFivePrimes.expCircle (alpha * d * w) * (TaoFivePrimes.eta0 ((d : ℝ) * w / x) : ℂ)
        else 0)) ∧
    (∃ c : ℕ → ℂ,
      (∀ d ∈ TaoFivePrimes.theorem51Divisors U V, ‖c d‖ ≤ 1) ∧
      ‖TaoFivePrimes.eta0VaughanTypeISum x alpha U V‖ ≤
        ∑ d ∈ TaoFivePrimes.theorem51Divisors U V, ‖
          (if d ≤ ⌊U⌋₊
            then ∑ w ∈ TaoFivePrimes.TypeIOuterDAssembly.fullInnerSupport x d,
                   ((Real.log (w : ℝ) : ℂ) * TaoFivePrimes.eta0VaughanTest x alpha (d * w))
            else ∑ w ∈ TaoFivePrimes.TypeIOuterDAssembly.transferredInnerSupport x V d,
                   ((Real.log (w : ℝ) : ℂ) * TaoFivePrimes.eta0VaughanTest x alpha (d * w)))
          + c d * (Real.log d : ℂ) *
              (∑ w ∈ TaoFivePrimes.TypeIOuterDAssembly.fullInnerSupport x d,
                TaoFivePrimes.eta0VaughanTest x alpha (d * w))‖) := by
  have h1 :=
    TaoFivePrimes.smoothedExpSum_eq_eta0VaughanTypeISum_add_centredPairSum
      x alpha U V hU hV hUx hVx hUVx hUV2
  obtain ⟨c, hc, hEV⟩ :=
    TaoFivePrimes.theorem51_child3_restricted_log_repair
      x alpha U V hU hV hUx hVx hUVx hUV2
  exact ⟨h1, c, hc, hEV⟩
