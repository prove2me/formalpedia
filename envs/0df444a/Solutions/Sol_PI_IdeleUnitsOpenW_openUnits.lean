-- Prove2me | solution 1 for PI.IdeleUnitsOpenW.openUnits
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:05:36.268463+00:00
-- url     : https://prove2.me/submissions/9cc9402f-7704-4f9d-bb22-94fe2795e495

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_CharExGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdeleUnitsOpen_IsOpenAdicCompletionIntegers
import Theorems.Thm_PI_IdeleUnitsOpenW_isOpen_integralAdeles
import Theorems.Thm_PI_IdeleUnitsOpenW_unitIdeles_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR
open PI PI.IdeleUnitsOpenW
variable (L : Type) [Field L] [NumberField L]
namespace PI.IdeleUnitsOpenW
theorem _root_.solution : Formalism.L2.Host.CharEx.OpenUnits L := by
  show IsOpen (Formalism.L2.Host.CharEx.unitIdeles L : Set (Ideles L))
  rw [unitIdeles_eq]
  exact ((isOpen_integralAdeles L).preimage Units.continuous_val).inter
    ((isOpen_integralAdeles L).preimage (Units.continuous_val.comp continuous_inv))
end PI.IdeleUnitsOpenW
