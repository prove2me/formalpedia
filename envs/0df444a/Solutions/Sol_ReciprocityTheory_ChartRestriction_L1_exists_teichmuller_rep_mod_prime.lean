-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.exists_teichmuller_rep_mod_prime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:43:02.388026+00:00
-- url     : https://prove2.me/submissions/6ef43390-87d7-466a-b20c-cf7477a80e39

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ExistsPowerMulUnitNorm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ExistsTeichmullerRepModPrime
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_norm_prime_lt_one_complexPadic
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_rmu_frob
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_rmu_norm_le
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_tch_near


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
theorem _root_.solution {a : ℂ_[l]} (ha : a ∈ Rmu l) : ∃ ξ ∈ Tch l, ‖a - ξ‖ ≤ ‖(l : ℂ_[l])‖ := by
  obtain ⟨f, hf, r, hr, h⟩ := rmu_frob l a ha
  refine tch_near l a (rmu_norm_le l ha) f hf _ (norm_prime_lt_one_complexPadic l) ?_
  rw [h, norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (rmu_norm_le l hr)
end ReciprocityTheory.ChartRestriction.L1
