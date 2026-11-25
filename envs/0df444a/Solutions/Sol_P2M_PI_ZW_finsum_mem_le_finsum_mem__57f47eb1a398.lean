-- Prove2me | solution 1 for P2M_PI_ZW_finsum_mem_le_finsum_mem__57f47eb1a398
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:50:34.793814+00:00
-- url     : https://prove2.me/submissions/68800f62-d518-4346-846e-52dcfa348897

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
theorem _root_.solution {s : Set ℂ} (f g : ℂ → ℝ) (hs : s.Finite) (h : ∀ x ∈ s, f x ≤ g x) :
    ∑ᶠ x ∈ s, f x ≤ ∑ᶠ x ∈ s, g x := by
  rw [finsum_mem_eq_finite_toFinset_sum _ hs, finsum_mem_eq_finite_toFinset_sum _ hs]
  exact Finset.sum_le_sum fun x hx => h x (hs.mem_toFinset.mp hx)
end PI.ZW
