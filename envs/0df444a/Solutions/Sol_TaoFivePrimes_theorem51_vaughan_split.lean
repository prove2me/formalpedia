-- Prove2me | solution 1 for TaoFivePrimes.theorem51_vaughan_split
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-21T08:24:55.542889+00:00
-- url     : https://prove2.me/submissions/80350542-4cca-4ef5-9bcc-a8034c80a0a1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_TaoFivePrimes_theorem51_vaughan_split_centred_assembly

theorem solution (x alpha U V : ℝ) (hU : 40 ≤ U) (hV : 40 ≤ V)
    (hUx : U < x) (hVx : V < x)
    (hUVx : U * V ≤ x / 4) (hUV2 : x ≤ U * V ^ 2) :
    ∃ c : ℕ → ℂ,
      (∀ d ∈ TaoFivePrimes.theorem51Divisors U V, ‖c d‖ ≤ 1) ∧
      ‖TaoFivePrimes.smoothedExpSum TaoFivePrimes.eta0 2 x alpha‖ ≤
        TaoFivePrimes.theorem51TypeI x alpha U V c +
          TaoFivePrimes.theorem51TypeII x alpha U V := by
  obtain ⟨h1, h3⟩ := TaoFivePrimes.theorem51_vaughan_split_centred_assembly
    x alpha U V hU hV hUx hVx hUVx hUV2
  obtain ⟨c, hc, hcmp⟩ := h3
  refine ⟨c, hc, ?_⟩
  rw [h1, TaoFivePrimes.theorem51TypeII]
  exact le_trans (norm_add_le _ _) (add_le_add_left hcmp _)
