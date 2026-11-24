-- Prove2me | solution 2 for TaoFivePrimes.theorem51_vaughan_split_centred_assembly
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T05:19:58.759154+00:00
-- url     : https://prove2.me/submissions/a40a0b85-7295-4ba4-afed-7ad1ca675830
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_TaoFivePrimes_SmoothedExpSum
import Definitions.Def_TaoFivePrimes_Theorem51Sums
import Theorems.Thm_TaoFivePrimes_smoothedExpSum_eq_eta0VaughanTypeISum_add_centredPairSum
import Theorems.Thm_TaoFivePrimes_eta0VaughanTypeISum_le_theorem51TypeI

theorem _root_.solution
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
        TaoFivePrimes.theorem51TypeI x alpha U V c) :=
  ⟨TaoFivePrimes.smoothedExpSum_eq_eta0VaughanTypeISum_add_centredPairSum
      x alpha U V hU hV hUx hVx hUVx hUV2,
   TaoFivePrimes.eta0VaughanTypeISum_le_theorem51TypeI
      x alpha U V hU hV hUx hVx hUVx hUV2⟩

#print axioms solution
