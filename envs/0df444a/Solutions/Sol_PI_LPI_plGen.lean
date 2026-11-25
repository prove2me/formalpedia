-- Prove2me | solution 1 for PI.LPI.plGen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:13:43.824196+00:00
-- url     : https://prove2.me/submissions/c7dc6a90-eb0d-4495-9a08-0056618a42a4

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_StatementC
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelProductIndex_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelProductIndex_ZeroMemLatSet
import Theorems.Thm_PI_UnitaryGroupMassFormula_LevelProdIdx_mem_latS_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix NumberField IsDedekindDomain
open scoped TensorProduct
noncomputable section
open PI PI.LPI
namespace PI.LPI
theorem _root_.solution : PLGen := by
  intro F E _ _ _ _ _ R _ _ O n k Lb m hm hLb y
  exact PI.UnitaryGroupMassFormula.LevelProdIdx.mem_latS_iff R O Lb m hm hLb y
end PI.LPI
