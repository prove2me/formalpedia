-- Prove2me | solution 1 for PI.Dv.TIW.norm_chiT_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:35:48.066443+00:00
-- url     : https://prove2.me/submissions/a1dddddc-5f6b-4bc5-8ecd-72460e278a45

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_PerS
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_GroupDataExists
import Theorems.Thm_PI_Dv_TIW_card_H_pos
import Theorems.Thm_PI_Dv_TIW_chiT_of_mem
import Theorems.Thm_PI_Dv_TIW_chiT_of_not_mem
import Theorems.Thm_PI_Dv_TIW_chi_inv_pow


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.TIW
open PI.Dv NumberField
variable {K : Type} [Field K] [NumberField K] {G : Type} [Group G] [Fintype G]
namespace PI.Dv.TIW
theorem _root_.solution (P : Pair K G) (x : G) (σ : K →+* ℂ) : ‖σ (chiT P x)‖ ≤ 1 := by
  by_cases hx : x ∈ P.H
  · rw [chiT_of_mem P x hx]
    have h := chi_inv_pow P ⟨x, hx⟩
    have h2 : (σ (((P.chi ⟨x, hx⟩)⁻¹ : Kˣ) : K)) ^ (Nat.card P.H) = 1 := by rw [← map_pow, h, map_one]
    exact (Complex.norm_eq_one_of_pow_eq_one h2 (card_H_pos P).ne').le
  · rw [chiT_of_not_mem P x hx, map_zero, norm_zero]; exact zero_le_one
end PI.Dv.TIW
