-- Prove2me | solution 1 for PI.UnitaryCorollaryDerivatives.DjC.presR
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:53:51.237327+00:00
-- url     : https://prove2.me/submissions/d8c0c81f-0dd5-4568-aadf-150228e3ea0a

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_DjCurveA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_DjCurveB
import Theorems.Thm_PI_UnitaryCorollaryDerivatives_DjC_mem_range_eR

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
variable {k j ρ}
namespace PI.UnitaryCorollaryDerivatives.DjC
theorem _root_.solution {Y : B.Mat k (j + ρ)} (hY : inLieP k j ρ Y) : Pres (Set.range (eR k j ρ)) Y := by
  intro c b hb hc
  rw [mem_range_eR] at hb hc
  exact hY.2 c b hb (not_lt.1 hc)
end PI.UnitaryCorollaryDerivatives.DjC
