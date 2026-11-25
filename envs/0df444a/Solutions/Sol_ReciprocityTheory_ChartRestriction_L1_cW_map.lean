-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.cW_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:42:49.490669+00:00
-- url     : https://prove2.me/submissions/bdc53d13-30b4-43a5-b1f2-0d72badeba61

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_CoeffOneSubstOfConstantCoeffEqZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_cW_unfold

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM
variable {K L : Type} [Field K] [Field L] (φ : K →+* L) (g2 g3 : K)
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution (k : ℕ) : φ (cW g2 g3 k) = cW (φ g2) (φ g3) k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rw [cW_unfold, cW_unfold (φ g2) (φ g3)]
    split_ifs with h1 h2 h3
    · rw [map_div₀]
      congr 1
      exact_mod_cast map_natCast φ 20
    · rw [map_div₀]
      congr 1
      exact_mod_cast map_natCast φ 28
    · simp only [map_mul, map_div₀, map_sum, map_ofNat, map_natCast, map_sub, map_add, map_one]
      congr 1
      refine Finset.sum_congr rfl fun m _ => ?_
      have hm := m.2
      rw [ih _ (by omega), ih _ (by omega)]
    · simp
end ReciprocityTheory.ChartRestriction.L1
