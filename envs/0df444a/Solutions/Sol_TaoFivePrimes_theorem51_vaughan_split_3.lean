-- Prove2me | solution 3 for TaoFivePrimes.theorem51_vaughan_split
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T05:23:37.297912+00:00
-- url     : https://prove2.me/submissions/943b40bc-949a-4e9b-89ff-03ca9f53ac35
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_TaoFivePrimes_SmoothedExpSum
import Definitions.Def_TaoFivePrimes_Theorem51Sums
import Theorems.Thm_TaoFivePrimes_theorem51_vaughan_split_centred_assembly

theorem _root_.solution
    (x alpha U V : ℝ) (hU : 40 ≤ U) (hV : 40 ≤ V)
    (hUx : U < x) (hVx : V < x)
    (hUVx : U * V ≤ x / 4) (hUV2 : x ≤ U * V ^ 2) :
    ∃ c : ℕ → ℂ,
      (∀ d ∈ TaoFivePrimes.theorem51Divisors U V, ‖c d‖ ≤ 1) ∧
      ‖TaoFivePrimes.smoothedExpSum TaoFivePrimes.eta0 2 x alpha‖ ≤
        TaoFivePrimes.theorem51TypeI x alpha U V c +
          TaoFivePrimes.theorem51TypeII x alpha U V := by
  obtain ⟨heq, c, hc, hI⟩ :=
    TaoFivePrimes.theorem51_vaughan_split_centred_assembly x alpha U V hU hV hUx hVx hUVx hUV2
  refine ⟨c, hc, ?_⟩
  rw [heq]
  exact le_trans (norm_add_le _ _) (add_le_add hI le_rfl)

#print axioms solution
