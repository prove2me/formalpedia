-- Prove2me | solution 1 for PI.LocalEndW.localEndHomeo_of_three
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:11:02.856558+00:00
-- url     : https://prove2.me/submissions/923b85aa-35a8-44b4-b48f-af5d52eda9ed

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalEndomorphisms_LocalEndHomeoOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalEndomorphisms_IsUniformInducingOfVal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalEndomorphisms_AlgebraMapMemRange
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalEndomorphisms_Assembly
import Theorems.Thm_PI_LocalEndW_localEndHomeo_of
import Theorems.Thm_PI_LocalEndW_valContinuous
import Theorems.Thm_PI_LocalEndW_valSurjective


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.LocalEndW
namespace PI.LocalEndW
theorem _root_.solution (hA : HenselRoot) (hB1 : IntOfHensel) (hB2 : ValOfInt) :
    PI.LocalEndHomeo :=
  localEndHomeo_of hA hB1 hB2 valContinuous valSurjective
end PI.LocalEndW
