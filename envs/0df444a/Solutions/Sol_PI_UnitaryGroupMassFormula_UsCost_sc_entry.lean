-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UsCost.sc_entry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:03:56.39722+00:00
-- url     : https://prove2.me/submissions/d729e0b6-4593-4ae0-8b1d-58cbb127ae3c

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_LetterSize
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_EntryLeLsz
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_lsz_pos
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_entry_le_lsz

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UsCost
namespace PI.UnitaryGroupMassFormula.UsCost
theorem _root_.solution {k r : ℕ} (X : B.Mat k r) (a b : Fin (2 * r + k + 1)) : ‖sc X a b‖ ≤ 1 := by
  have hp := lsz_pos X
  have h := entry_le_lsz X a b
  have e : sc X a b = (((lsz X)⁻¹ : ℝ) : ℂ) * X a b := rfl
  rw [e, norm_mul, Complex.norm_of_nonneg (inv_nonneg.2 hp.le), inv_mul_le_iff₀ hp, mul_one]
  exact h
end PI.UnitaryGroupMassFormula.UsCost
