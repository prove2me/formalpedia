-- Prove2me | solution 1 for TaoFivePrimes.theorem51_unit_numerator_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-09-12T17:08:29.706963+00:00
-- url     : https://prove2.me/submissions/5bd1af4a-f623-40c7-9293-b97b334da035
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_TaoFivePrimes_theorem51_vaughan_split
import Theorems.Thm_TaoFivePrimes_theorem51_typeI_bound
import Theorems.Thm_TaoFivePrimes_theorem51_typeII_bound

theorem solution
    (x alpha beta U V : ℝ) (a : ℤ) (q : ℕ)
    (hq : 4 ≤ q) (haq : Nat.Coprime a.natAbs q) (haunit : a.natAbs = 1)
    (halpha : 4 * alpha = (a : ℝ) / q + beta)
    (hbeta : |beta| ≤ 1 / (q : ℝ) ^ 2)
    (hU40 : 40 ≤ U) (hV40 : 40 ≤ V) (hUx : U < x) (hVx : V < x)
    (hUV : U * V ≤ x / 4) (hUV2 : x ≤ U * V ^ 2)
    (hUVq : U * V < (q : ℝ) - 1) :
    ‖TaoFivePrimes.smoothedExpSum TaoFivePrimes.eta0 2 x alpha‖ ≤
      (96 / Real.pi ^ 2) * (x / (x / q) ^ 2) *
          Real.log (4 * x) * Real.log (4 * Real.exp 1 * q / Real.pi) +
        (0.1 * (x / Real.sqrt q) + 0.39 * (x / Real.sqrt (x / q))) *
          Real.log (x / (U * V)) * Real.log (V * x / U) +
        (0.55 * (x / Real.sqrt U) + 0.78 * (x / Real.sqrt V)) *
          Real.log (x / U) := by
  obtain ⟨c, hc, hsplit⟩ := TaoFivePrimes.theorem51_vaughan_split x alpha U V
    hU40 hV40 hUx hVx hUV hUV2
  have hI := TaoFivePrimes.theorem51_typeI_bound x alpha beta U V a q c
    hU40 hV40 hUV hUVq haunit hc halpha hbeta
  have hII := TaoFivePrimes.theorem51_typeII_bound x alpha beta U V a q
    hq haq haunit halpha hbeta hU40 hV40 hUx hVx hUV hUV2 hUVq
  exact hsplit.trans (by simpa only [add_assoc] using add_le_add hI hII)

