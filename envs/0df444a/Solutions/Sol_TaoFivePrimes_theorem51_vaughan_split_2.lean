-- Prove2me | solution 2 for TaoFivePrimes.theorem51_vaughan_split
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-21T11:35:04.727385+00:00
-- url     : https://prove2.me/submissions/64a20916-bc66-412a-a059-b1e18bfb68ef
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_TaoFivePrimes_Theorem51Sums
import Definitions.Def_TaoFivePrimes_TypeIEnvelopeInterfaces
import Theorems.Thm_TaoFivePrimes_smoothedExpSum_eq_eta0VaughanTypeISum_add_centredPairSum
import Theorems.Thm_TaoFivePrimes_eta0VaughanTypeISum_le_theorem51TypeI

set_option autoImplicit false

/-! The centred Vaughan split for the smoothed exponential sum, Tao
    arXiv:1201.6656 §5. By the (proved) centred decomposition identity,
    the smoothed sum equals the Type I part plus the centred pair double
    sum; `TaoFivePrimes.theorem51TypeII` is *by definition* the norm of
    that double sum, and the Type I part is dominated by the Type I
    interface envelope with bounded coefficients
    (`eta0VaughanTypeISum_le_theorem51TypeI`). The split follows by the
    triangle inequality. -/

theorem solution
    (x alpha U V : ℝ) (hU : 40 ≤ U) (hV : 40 ≤ V)
    (hUx : U < x) (hVx : V < x)
    (hUVx : U * V ≤ x / 4) (hUV2 : x ≤ U * V ^ 2) :
    ∃ c : ℕ → ℂ,
      (∀ d ∈ TaoFivePrimes.theorem51Divisors U V, ‖c d‖ ≤ 1) ∧
      ‖TaoFivePrimes.smoothedExpSum TaoFivePrimes.eta0 2 x alpha‖ ≤
        TaoFivePrimes.theorem51TypeI x alpha U V c +
          TaoFivePrimes.theorem51TypeII x alpha U V := by
  obtain ⟨c, hc1, hc2⟩ :=
    TaoFivePrimes.eta0VaughanTypeISum_le_theorem51TypeI x alpha U V hU hV hUx hVx hUVx hUV2
  refine ⟨c, hc1, ?_⟩
  have hEq := TaoFivePrimes.smoothedExpSum_eq_eta0VaughanTypeISum_add_centredPairSum
    x alpha U V hU hV hUx hVx hUVx hUV2
  rw [hEq]
  exact (norm_add_le _ _).trans (add_le_add hc2 (le_refl _))
