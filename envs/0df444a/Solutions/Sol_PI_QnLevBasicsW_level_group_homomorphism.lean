-- Prove2me | solution 1 for PI.QnLevBasicsW.level_group_homomorphism
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:21:24.66272+00:00
-- url     : https://prove2.me/submissions/88732e24-e88c-4dd0-9d4f-8859f1f31e67

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelLiftBasics_SplitInvInjective
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelLiftBasics_LevelGroupUnitaryHermitian
import Theorems.Thm_P2M_PI_QnLevBasicsW__Lev_eq_c687ca9a93c5


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open PI PI.QnLevBasicsW
open Formalism.QuantumDeterminants
variable {k i r' : ℕ}
namespace PI.QnLevBasicsW
theorem _root_.solution : LevHom := by
  intro k i r'
  refine ⟨?_, fun g h => ?_⟩
  · rw [ιLev_eq, Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]
  · rw [ιLev_eq, ιLev_eq, ιLev_eq, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
    simp
end PI.QnLevBasicsW
