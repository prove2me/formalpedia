-- Prove2me | solution 1 for PI.FockOneDegW.Swap.linePos_sw
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:12:31.963868+00:00
-- url     : https://prove2.me/submissions/8ae72d0d-94e7-4e54-92ef-6793f8f5291f

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_OneDegOfHalves
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_OmEDiagMonomial
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_KroneckerOneRightSwap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix FockH1Action MvPolynomial
open PI PI.FockOneDegW PI.FockOneDegW.Swap
open PI.FockOneDegW PI.FockOneDegW.Diag
variable {p q r s : ℕ}
namespace PI.FockOneDegW.Swap
theorem _root_.solution (l : Ln p q r s) : linePos (sw p q r s l) = linePos l := by
  rcases l with ⟨a | a, b | b⟩ <;> rfl
end PI.FockOneDegW.Swap
