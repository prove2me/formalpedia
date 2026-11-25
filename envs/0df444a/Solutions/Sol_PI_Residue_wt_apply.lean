-- Prove2me | solution 1 for PI.Residue.wt_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:12:52.234914+00:00
-- url     : https://prove2.me/submissions/ad11d9fb-6b99-40cb-a38f-18e1300463f6

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_HeckeLower
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_UnderEqOfNotCoprime
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_NnrealOfEnnreal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.Residue
open NumberField
open scoped ENNReal NNReal
namespace PI.Residue
theorem _root_.solution (s : ℝ) (n : ℕ) : wt s n = (((n : ℝ≥0) ^ (-s) : ℝ≥0) : ℝ≥0∞) := rfl
end PI.Residue
