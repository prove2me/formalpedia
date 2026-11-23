-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.rmu_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:41:57.154446+00:00
-- url     : https://prove2.me/submissions/c2076e34-121a-49a8-8096-ccf6fa14663e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FrobFixNegOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_NormNatCastClOfNotDvd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ExistsPowerMulUnitNorm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_muP_norm


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
variable (l : ℕ) [Fact l.Prime]
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution {x : ℂ_[l]} (hx : x ∈ Rmu l) : ‖x‖ ≤ 1 := by
  induction hx using Subring.closure_induction with
  | mem x hx => exact (muP_norm l hx).le
  | zero => simp
  | one => simp
  | add x y _ _ hx hy =>
    exact (IsUltrametricDist.norm_add_le_max x y).trans (max_le hx hy)
  | neg x _ hx => rwa [norm_neg]
  | mul x y _ _ hx hy =>
    rw [norm_mul]
    exact mul_le_one₀ hx (norm_nonneg _) hy
end ReciprocityTheory.ChartRestriction.L1
