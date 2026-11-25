-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.LCG.lattice_is_discrete_group
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:08:58.319872+00:00
-- url     : https://prove2.me/submissions/26502697-5d79-4bf2-8b9c-8198a1f1daf0

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_SepDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeSizeContinuity_LatticeIsometry
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_LatticeIsDiscreteGroup
import Theorems.Thm_PI_UnitaryGroupMassFormula_LSC_lattice_isometry


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.LCG
open PI.LatCountG
namespace PI.UnitaryGroupMassFormula.LCG
theorem _root_.solution : LatIsG := by
  intro I x
  obtain ⟨Λ, h1, h2, h3⟩ := PI.UnitaryGroupMassFormula.LSC.lattice_isometry I x
  exact ⟨Λ, h1, h2, h3⟩
end PI.UnitaryGroupMassFormula.LCG
