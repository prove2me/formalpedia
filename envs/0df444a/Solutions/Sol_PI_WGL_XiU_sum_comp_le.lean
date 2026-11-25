-- Prove2me | solution 1 for PI.WGL.XiU.sum_comp_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:11:55.588594+00:00
-- url     : https://prove2.me/submissions/cd3e1c00-6d68-4bb1-b0c3-d183fae5d2d9

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
theorem _root_.solution {N s : ℕ} (I : Fin s → Fin N) (hI : Function.Injective I) (f : Fin N → ℝ)
    (hf : ∀ a, 0 ≤ f a) : ∑ p, f (I p) ≤ ∑ a, f a := by
  rw [← Finset.sum_image (fun p _ q _ h => hI h)]
  exact Finset.sum_le_univ_sum_of_nonneg hf
end PI.WGL.XiU
