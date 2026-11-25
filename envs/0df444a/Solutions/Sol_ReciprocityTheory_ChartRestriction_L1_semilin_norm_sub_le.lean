-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.semilin_norm_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:40:17.974942+00:00
-- url     : https://prove2.me/submissions/ddb29191-5eee-42b8-a2f3-84c0ade8dfbf

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_KurDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_SemilinNormPowSubPow

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
open Formalism.L2.Th1.CM
variable {K : Type} [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [CharZero K]
omit [CompleteSpace K] [CharZero K]
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution {a b : K} {t : ℝ} (ha : ‖a‖ ≤ t) (hb : ‖b‖ ≤ t) : ‖a - b‖ ≤ t := by
  rw [sub_eq_add_neg]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha (by rwa [norm_neg]))
end ReciprocityTheory.ChartRestriction.L1
