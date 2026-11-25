-- Prove2me | solution 1 for P2M_PI_ZW_finsum_mem_le_of_subset__d846247134c2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:50:40.112143+00:00
-- url     : https://prove2.me/submissions/7c96b4b6-9996-4567-a96f-17d04a385575

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZeroWindow_RightHalfWith
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZeroWindow_FinsumMemLeFinsumMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.ZW
open DirichletCharacter
namespace PI.ZW
theorem _root_.solution {s t : Set ℂ} (g : ℂ → ℝ) (hg : ∀ x, 0 ≤ g x) (ht : t.Finite)
    (hst : s ⊆ t) : ∑ᶠ x ∈ s, g x ≤ ∑ᶠ x ∈ t, g x := by
  rw [finsum_mem_eq_finite_toFinset_sum _ (ht.subset hst), finsum_mem_eq_finite_toFinset_sum _ ht]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Set.Finite.toFinset_subset_toFinset.mpr hst) fun x _ _ => hg x
end PI.ZW
