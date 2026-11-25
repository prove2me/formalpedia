-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UJClassMass.surjStep_of_patchF_herm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:27:53.571794+00:00
-- url     : https://prove2.me/submissions/a874ebab-8250-4b81-9194-c888e7f7ca61

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_PSurjF
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_PSurjS
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_semiApprox_of
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_surjStep_of_F


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField PI.UJClassFin PI.UJClassMass Formalism.HermitianLatticesTheory IsDedekindDomain
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UJClassMass
namespace PI.UnitaryGroupMassFormula.UJClassMass
theorem _root_.solution (hP : PatchF) (hH : HermApprox) (hO : LSOne) : SurjStep :=
  surjStep_of_F hP (semiApprox_of hH) hO
end PI.UnitaryGroupMassFormula.UJClassMass
