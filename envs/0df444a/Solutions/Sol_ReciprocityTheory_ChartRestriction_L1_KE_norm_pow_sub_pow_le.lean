-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.KE.norm_pow_sub_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:33:49.612086+00:00
-- url     : https://prove2.me/submissions/1e96af8d-a9e1-4d91-8e52-65674805890e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ExistsTeichmullerRepModPrime
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_NormLeOneOfIntegralInt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1 ReciprocityTheory.ChartRestriction.L1.KE
open Formalism.L2.Th1.CM
namespace ReciprocityTheory.ChartRestriction.L1.KE
theorem _root_.solution {K : Type*} [NormedField K] [IsUltrametricDist K] {x y : K}
    (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) (i : ℕ) : ‖x ^ i - y ^ i‖ ≤ ‖x - y‖ := by
  induction i with
  | zero => simp
  | succ i ih =>
    have : x ^ (i + 1) - y ^ (i + 1) = x * (x ^ i - y ^ i) + (x - y) * y ^ i := by ring
    rw [this]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [norm_mul]
      calc ‖x‖ * ‖x ^ i - y ^ i‖ ≤ 1 * ‖x - y‖ := by gcongr
        _ = _ := one_mul _
    · rw [norm_mul, norm_pow]
      calc ‖x - y‖ * ‖y‖ ^ i ≤ ‖x - y‖ * 1 := by
            gcongr; exact pow_le_one₀ (norm_nonneg _) hy
        _ = _ := mul_one _
end ReciprocityTheory.ChartRestriction.L1.KE
