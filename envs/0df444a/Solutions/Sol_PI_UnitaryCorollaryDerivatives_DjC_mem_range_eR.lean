-- Prove2me | solution 1 for PI.UnitaryCorollaryDerivatives.DjC.mem_range_eR
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:39:08.126615+00:00
-- url     : https://prove2.me/submissions/692a427b-d319-4bba-9778-932a5d3b4256

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_DjCurveA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_DjCurveB

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
theorem _root_.solution (c : Fin (2 * (j + ρ) + k + 1)) : c ∈ Set.range (eR k j ρ) ↔ c.val < j := by
  constructor
  · rintro ⟨a, rfl⟩
    exact a.2
  · intro h
    exact ⟨⟨c.val, h⟩, Fin.ext rfl⟩
end PI.UnitaryCorollaryDerivatives.DjC
