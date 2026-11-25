-- Prove2me | solution 1 for PI.Residue.tsum_le_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:19:14.922891+00:00
-- url     : https://prove2.me/submissions/2872f23f-ae32-4c3e-b60a-e6fa922ecf27

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_FactorizationMultisetProd
import Theorems.Thm_PI_Residue_tsum_pi_prod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.Residue
open scoped ENNReal
namespace PI.Residue
theorem _root_.solution {β : Type*} {m : ℕ} (n : β → Fin m → ℕ) (hinj : Function.Injective n)
    (w : ℕ → ℝ≥0∞) (W : β → ℝ≥0∞) (hw : ∀ b, W b = ∏ i, w (n b i)) :
    ∑' b, W b ≤ (∑' k, w k) ^ m := by
  rw [← tsum_pi_prod]
  simp_rw [hw]
  exact ENNReal.tsum_comp_le_tsum_of_injective hinj (fun v => ∏ i, w (v i))
end PI.Residue
