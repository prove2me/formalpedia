-- Prove2me | solution 1 for PI.WGL.XiU.multiset_prod_norm_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:14:23.512177+00:00
-- url     : https://prove2.me/submissions/b96372f1-3bf2-47bf-b0a8-baf266e8193c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_MultisetProdNormLeOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WGL PI.WGL.XiU
open Matrix
namespace PI.WGL.XiU
theorem _root_.solution (m : Multiset ℂ) (h : ∀ μ ∈ m, ‖μ‖ ≤ 1) : ‖m.prod‖ ≤ 1 := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.prod_cons, norm_mul]
    have ha := h a (by simp)
    have hs := ih (fun μ hμ => h μ (by simp [hμ]))
    exact mul_le_one₀ ha (norm_nonneg _) hs
end PI.WGL.XiU
