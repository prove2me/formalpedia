-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnitDetRoot.detInK
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:07:29.677711+00:00
-- url     : https://prove2.me/submissions/da4483ab-9aad-4882-9171-818db0f54b61

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitDeterminantRoot_NsmulRelIdxMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitDeterminantRoot_DetMemOfEntries
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnitDetRoot_det_mem_of_entries
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnitDetRoot_entries_mem
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnitDetRoot_unitary_det

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped ComplexConjugate
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UnitDetRoot
open PI
namespace PI.UnitaryGroupMassFormula.UnitDetRoot
theorem _root_.solution : DetInK := by
  intro a b c d ha hd lam hlam m _ _ Λa hH δ hA
  refine ⟨?_, unitary_det hA.1⟩
  rw [← LinearMap.det_toMatrix']
  exact det_mem_of_entries _ (entries_mem hH hA)
end PI.UnitaryGroupMassFormula.UnitDetRoot
