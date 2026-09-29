-- Prove2me | solution 1 for TateCurve.nnnorm_c4
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/3ee6b374-ab1a-5049-8985-57af99642e84

import Definitions.Def_TateCurve_QSeries
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_TateCurve_nnnorm_c4
open scoped NNReal
open TateCurve IsUltrametricDist

theorem solution {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    {q : K} (hq : ‖q‖₊ < 1) : ‖(curve q).c₄‖₊ = 1 := by
  have h : ‖(curve q).c₄ - 1‖₊ < 1 := by
    rw [curve_c₄]
    have heq : (1 : K) - 48 * a₄ q - 1 = -(48 * a₄ q) := by ring
    rw [heq, nnnorm_neg, nnnorm_mul]
    calc ‖(48 : K)‖₊ * ‖a₄ q‖₊ ≤ 1 * ‖q‖₊ := by
          gcongr
          · exact_mod_cast nnnorm_natCast_le_one K 48
          · exact nnnorm_a₄_le hq
      _ = ‖q‖₊ := one_mul _
      _ < 1 := hq
  have h2 := nnnorm_eq_of_nnnorm_sub_lt (a := (curve q).c₄) (b := (1 : K)) (by rw [nnnorm_one]; exact h)
  rwa [nnnorm_one] at h2

end S_TateCurve_nnnorm_c4
end P2MW
export P2MW.S_TateCurve_nnnorm_c4 (solution)
