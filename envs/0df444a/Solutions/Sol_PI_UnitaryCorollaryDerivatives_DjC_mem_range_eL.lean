-- Prove2me | solution 1 for PI.UnitaryCorollaryDerivatives.DjC.mem_range_eL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:59:04.40403+00:00
-- url     : https://prove2.me/submissions/0eb64e47-515f-4266-b4e0-44e77475a0b6

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_DjCurveA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_DjCurveB
import Theorems.Thm_PI_UnitaryCorollaryDerivatives_DjC_eL_val

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open PI PI.UnitaryCorollaryDerivatives PI.UnitaryCorollaryDerivatives.DjC
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U
variable (k j ρ : ℕ)
namespace PI.UnitaryCorollaryDerivatives.DjC
theorem _root_.solution (c : Fin (2 * (j + ρ) + k + 1)) :
    c ∈ Set.range (eL k j ρ) ↔ 2 * (j + ρ) + k + 1 ≤ c.val + j := by
  have hc := c.isLt
  constructor
  · rintro ⟨a, rfl⟩
    rw [eL_val]
    have := a.isLt
    omega
  · intro h
    refine ⟨⟨2 * (j + ρ) + k - c.val, by omega⟩, Fin.ext ?_⟩
    rw [eL_val]
    simp only
    omega
end PI.UnitaryCorollaryDerivatives.DjC
