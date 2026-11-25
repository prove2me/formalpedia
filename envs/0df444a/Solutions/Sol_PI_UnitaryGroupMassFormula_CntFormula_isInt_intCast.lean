-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.CntFormula.isInt_intCast
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:38:07.990116+00:00
-- url     : https://prove2.me/submissions/68972ff7-8358-45f3-8a04-fb43bc6640be

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CountingFormula_IsIntIntCast

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.CntFormula
open NumberField
variable {K : Type} [Field K] [NumberField K]
namespace PI.UnitaryGroupMassFormula.CntFormula
theorem _root_.solution (n : ℤ) : IsIntegral ℤ (n : K) := by
  simpa using (isIntegral_algebraMap : IsIntegral ℤ (algebraMap ℤ K n))
end PI.UnitaryGroupMassFormula.CntFormula
