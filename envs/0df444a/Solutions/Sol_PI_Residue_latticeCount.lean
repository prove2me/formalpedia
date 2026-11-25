-- Prove2me | solution 1 for PI.Residue.latticeCount
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:19:03.620925+00:00
-- url     : https://prove2.me/submissions/35a27f2a-a12a-41dc-bcd0-4548769db97c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_UnitPreserving
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_LatticeCountGen
import Theorems.Thm_PI_Residue_latticeCount_gen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField NumberField.mixedEmbedding MeasureTheory
open scoped ENNReal Pointwise Classical
noncomputable section
open PI PI.Residue
namespace PI.Residue
theorem _root_.solution : LatticeCount := fun _ _ _ L _ _ B hB => latticeCount_gen volume L B hB
end PI.Residue
