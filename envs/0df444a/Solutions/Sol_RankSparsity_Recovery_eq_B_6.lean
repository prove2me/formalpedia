-- Prove2me | solution 1 for RankSparsity.Recovery.eq_B_6
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-10-21T06:41:50.204243+00:00
-- url     : https://prove2.me/submissions/ae3012b4-a563-4cff-bfb5-6280b1b31f22

import Definitions.Def_matrix_completion_tangent
import Definitions.Def_RankSparsity_Recovery_Setup
import Mathlib.Tactic.Linarith

set_option autoImplicit false
open MatrixCompletion

namespace Oct21FiveRankGamma

/-- An explicit positive gap separates the two candidate parameter bounds. -/
theorem scalar_gap (x m : ℝ) (h : x * m < 1 / 6) (hm : 0 < m) :
    x / (1 - 4 * x * m) < (1 - 3 * x * m) / m := by
  have hd : 0 < 1 - 4 * x * m := by nlinarith
  have h6 : 0 < 1 - 6 * x * m := by nlinarith
  have h2 : 0 < 1 - 2 * x * m := by nlinarith
  apply (div_lt_div_iff₀ hd hm).2
  nlinarith [mul_pos h6 h2]

end Oct21FiveRankGamma

/-- The parameter interval in the rank-sparsity recovery theorem is nonempty. -/
theorem solution {n r : ℕ} (Astar Bstar : RealMatrix n n) (S : SVD Bstar r)
    (h : RankSparsity.Recovery.xi S * RankSparsity.Recovery.mu Astar < 1 / 6)
    (hmu : 0 < RankSparsity.Recovery.mu Astar) :
    RankSparsity.Recovery.xi S / (1 - 4 * RankSparsity.Recovery.xi S * RankSparsity.Recovery.mu Astar) <
      (1 - 3 * RankSparsity.Recovery.xi S * RankSparsity.Recovery.mu Astar) / RankSparsity.Recovery.mu Astar := by
  exact Oct21FiveRankGamma.scalar_gap _ _ h hmu

#print axioms solution
